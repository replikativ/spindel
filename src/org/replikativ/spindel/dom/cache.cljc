(ns org.replikativ.spindel.dom.cache
  "Slot-based caching for DOM elements.

  Each parent element caches its children by slot position. This enables:
  - Stable slot indices (conditionals returning nil don't shift positions)
  - Efficient delta computation (compare prev slot vs new value)
  - KeyedFragment support (keyed lists at a slot position)

  Cache is stored in execution context state at [:dom/cache <address>].

  Slot Types:
  - :nil    - Slot is empty (conditional returned nil)
  - :single - Slot contains one vnode
  - :keyed  - Slot contains KeyedFragment (from ifor-each)"
  (:require [clojure.set]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.dom.core :as core]))

;; Forward declaration for KeyedFragment check
(declare keyed-fragment?)

;; =============================================================================
;; Slot Types
;; =============================================================================

(defn classify-slot
  "Classify a child result into a slot type.

  Returns: :nil, :single, or :keyed"
  [result]
  (cond
    (nil? result) :nil
    (keyed-fragment? result) :keyed
    (core/vnode? result) :single
    ;; Plain vectors treated as keyed (from raw ifor-each without wrapper)
    (vector? result) :keyed
    ;; Anything else treated as single (will be coerced to text node)
    :else :single))

(defn make-slot
  "Create a slot entry from a child result.

  Returns: {:type :nil|:single|:keyed :value <result>}"
  [result]
  {:type (classify-slot result)
   :value result})

;; =============================================================================
;; Cache Access
;; =============================================================================

(defn get-slot-cache
  "Get cached slots for an element address.

  Returns: Vector of slot entries, or nil if not cached."
  [addr]
  (ec/get-state [:dom/cache addr]))

(defn set-slot-cache!
  "Store slot cache for an element address.

  Args:
    addr - Element address (keyword)
    slots - Vector of {:type :value} slot entries"
  [addr slots]
  (ec/swap-state! [:dom/cache addr] (constantly slots)))

;; =============================================================================
;; Attribute Cache Access
;; =============================================================================

(defn get-attr-cache
  "Get cached attrs for an element address.

  Returns: Map of previous attribute values, or nil if not cached."
  [addr]
  (ec/get-state [:dom/attr-cache addr]))

(defn set-attr-cache!
  "Store attr cache for an element address.

  Args:
    addr - Element address (keyword)
    attrs - Map of attribute values"
  [addr attrs]
  (ec/swap-state! [:dom/attr-cache addr] (constantly attrs)))

;; =============================================================================
;; Staging — the caches model the DOM, so they advance on COMMIT, not on compute
;; =============================================================================
;;
;; A reconciliation writes its result HERE, not into the committed caches. The
;; committed caches are promoted only for addresses that appear in a vdom tree
;; that was actually discharged (`commit-pending!`, called from
;; `discharge-all!`).
;;
;; Why: a body slice can build its elements and then suspend on an `await`. If
;; a newer signal value resumes the track continuation above it, `resume-body!`
;; truncates and CANCELS that slice — its CPS chain never resolves, so its
;; vnode never reaches the render effect. Advancing the caches while computing
;; meant that abandoned run still moved the baseline: the next run reconciled
;; against a value the DOM had never been told about, produced no deltas, and
;; the change was lost with nothing logged.
;;
;; Worse, it compounded. A lost `:add` left the slot cache claiming a child the
;; DOM never gained, so the following transition removed the wrong index — a
;; live sibling — and every index after it was off by one.
;;
;; Staging makes abandonment free: a slice that never reaches the DOM never
;; moves the baseline.

(defn stage-attrs!
  "Stage reconciled attrs for `addr`. Promoted by `commit-pending!`."
  [addr attrs]
  (ec/swap-state! [:dom/pending addr] (fn [m] (assoc m :attrs attrs))))

(defn stage-slots!
  "Stage reconciled slots for `addr`. Promoted by `commit-pending!`."
  [addr slots]
  (ec/swap-state! [:dom/pending addr] (fn [m] (assoc m :slots slots))))

(defn stage-keyed!
  "Stage an `ifor-each` keyed cache for its call-site `addr`."
  [addr cache-data]
  (ec/swap-state! [:dom/pending addr] (fn [m] (assoc m :keyed cache-data))))

(defn- keyed-frag-addrs
  "The `ifor-each` call-site addresses reachable from `slots`.

   A `:keyed` slot holds a KeyedFragment whose `:addr` is the call site — an
   address that appears on NO vnode, because `flatten-slot` splices the
   fragment's items into `:children` and drops the fragment itself. The commit
   sweep walks vnodes, so it cannot see these; they are reached the same way
   `evict-cache!` reaches them, through the parent's slots."
  [slots]
  (into #{} (keep (fn [slot]
                    (when (= :keyed (:type slot))
                      (:addr (:value slot))))
                  slots)))

(defn live-keyed-closure
  "Extend `live-addrs` with the `ifor-each` call-site addresses reachable from
   their COMMITTED slots, transitively.

   The eviction counterpart to the closure `commit-pending!` runs over STAGED
   slots, and needed for the same reason: a fragment call site appears on no
   vnode, so a liveness set built from rendered vnodes never contains one.
   Without this, a fragment is structurally exempt from the very check that
   protects live addresses from eviction.

   `commit-pending!` runs before `flush-pending-evictions!` at every call site,
   so by eviction time the live tree's slots are already promoted here."
  [live-addrs]
  (loop [live (set live-addrs)]
    (let [more (into live
                     (mapcat #(keyed-frag-addrs (ec/get-state [:dom/cache %])))
                     live)]
      (if (= (count more) (count live)) live (recur more)))))

(defn commit-pending!
  "Promote staged cache entries for `live-addrs`, and drop the rest.

   `live-addrs` is every `:addr` in the vdom tree that was just discharged.
   An address that was staged by a run whose output never reached the DOM is
   absent from that set, so its staging is discarded and the committed cache
   keeps describing what the DOM actually holds.

   Fragment call sites are folded in transitively: they hang off a parent's
   `:keyed` slots rather than off any vnode, and a fragment's own items can in
   turn contain further fragments, so this closes over the staged slots until
   the live set stops growing."
  [live-addrs]
  (let [pending (ec/get-state [:dom/pending])]
    (when (seq pending)
      (let [live (loop [live (set live-addrs)]
                   (let [more (into live
                                    (mapcat (fn [addr]
                                              (keyed-frag-addrs (get-in pending [addr :slots])))
                                            live))]
                     (if (= (count more) (count live)) live (recur more))))]
        (doseq [[addr entry] pending
                :when (contains? live addr)]
          (when (contains? entry :attrs)
            (ec/swap-state! [:dom/attr-cache addr] (constantly (:attrs entry))))
          (when (contains? entry :slots)
            (ec/swap-state! [:dom/cache addr] (constantly (:slots entry))))
          (when (contains? entry :keyed)
            (ec/swap-state! [:dom/keyed-cache addr] (constantly (:keyed entry)))))
        ;; Drop ONLY what was promoted. Staging for addresses outside this tree
        ;; is kept, not discarded: a child spin resolves on its own schedule, so
        ;; it can stage its build one pass and have its vnode embedded by the
        ;; parent in a later one. Clearing wholesale destroyed that staging in
        ;; between, the child's cache never advanced, and it re-emitted `:add`
        ;; on the next build — duplicating its subtree (caught by
        ;; cross-spin-rerender and ifor-each-oscillation).
        ;;
        ;; Retained staging is not a leak: a rebuild overwrites its address,
        ;; `evict-cache!` drops it on unmount, and snapshot cleaning drops the
        ;; whole map.
        (ec/swap-state! [:dom/pending] (fn [m] (apply dissoc m (filter live (keys m)))))))))

(defn evict-cache!
  "Drop all per-address engine state for an element address.

  Called when an element is unmounted so the per-address entries do not
  accumulate for the lifetime of the context. Covers every `[:dom/* <addr>]`
  map the render path writes:
  - `:dom/cache`       — slot cache
  - `:dom/attr-cache`  — attribute cache
  - `:dom/keyed-cache` — `ifor-each` per-call-site keyed cache
  - `:dom/foreign`     — foreign-node marker

  Cascades into `ifor-each` keyed caches held by this element's slots. A
  `:keyed` slot stores a `KeyedFragment` whose `:addr` is the ifor-each CALL
  SITE — an address that appears on no vnode, because `flatten-slot` splices
  the fragment's items into `:children` and drops the fragment itself. Walking
  the vnode tree therefore cannot reach it. Without this cascade, unmounting a
  subtree containing an `ifor-each` retained `:by-key` (every rendered vnode,
  with its event-handler closures) for the lifetime of the context — the
  dominant leak in a long-lived session."
  ([addr] (evict-cache! addr nil))
  ([addr protected]
   (when addr
     (doseq [slot (ec/get-state [:dom/cache addr])
             :when (= :keyed (:type slot))]
       (when-let [frag-addr (:addr (:value slot))]
         ;; `protected` guards the cascade against a dead parent taking a LIVE
         ;; fragment's cache with it. The call-site address is stable across
         ;; re-renders, so a superseded parent's slots still name the fragment
         ;; the current parent renders; dropping it resets the keyed baseline to
         ;; empty and the next render re-adds every item. Measured before the
         ;; guard: a settled collapse turned 6 sections into 12.
         (when-not (contains? protected frag-addr)
           (ec/swap-state! [:dom/keyed-cache] (fn [m] (dissoc m frag-addr))))))
     (ec/swap-state! [:dom/cache] (fn [m] (dissoc m addr)))
     (ec/swap-state! [:dom/attr-cache] (fn [m] (dissoc m addr)))
     (ec/swap-state! [:dom/keyed-cache] (fn [m] (dissoc m addr)))
     (ec/swap-state! [:dom/foreign] (fn [m] (dissoc m addr)))
     ;; Staging too, or an unmounted address could be resurrected by a commit
     ;; sweep that runs after the eviction.
     (ec/swap-state! [:dom/pending] (fn [m] (dissoc m addr))))))

;; =============================================================================
;; Attribute Reconciliation
;; =============================================================================

(defn reconcile-attrs
  "Reconcile previous attrs with new attrs, producing deltas.

  Args:
    prev-attrs - Previous attribute map (or nil)
    new-attrs - New attribute map

  Returns: Vector of attribute deltas (or nil if no changes)"
  [prev-attrs new-attrs]
  (let [prev-attrs (or prev-attrs {})
        new-attrs (or new-attrs {})
        prev-keys (set (keys prev-attrs))
        new-keys (set (keys new-attrs))

        ;; Keys added (in new but not in prev)
        added-keys (clojure.set/difference new-keys prev-keys)

        ;; Keys removed (in prev but not in new)
        removed-keys (clojure.set/difference prev-keys new-keys)

        ;; Keys that exist in both - check for updates
        common-keys (clojure.set/intersection prev-keys new-keys)
        updated-keys (filter (fn [k]
                               (not= (get prev-attrs k) (get new-attrs k)))
                             common-keys)

        ;; Build deltas
        add-deltas (mapv (fn [k]
                           {:delta :add :path [k] :value (get new-attrs k)})
                         added-keys)
        remove-deltas (mapv (fn [k]
                              {:delta :remove :path [k] :old-value (get prev-attrs k)})
                            removed-keys)
        update-deltas (mapv (fn [k]
                              {:delta :update :path [k]
                               :old-value (get prev-attrs k)
                               :value (get new-attrs k)})
                            updated-keys)

        all-deltas (into [] (concat add-deltas remove-deltas update-deltas))]
    (when (seq all-deltas)
      all-deltas)))

;; =============================================================================
;; Slot Reconciliation
;; =============================================================================

(defn reconcile-slot
  "Reconcile a single slot, comparing prev vs new.

  Args:
    slot-index - Position in parent's children
    prev-slot - Previous slot entry {:type :value} or nil
    new-result - New child result (vnode, nil, or KeyedFragment)

  Returns: {:slot <new-slot-entry> :delta <delta-or-nil>}"
  [slot-index prev-slot new-result]
  (let [new-slot (make-slot new-result)
        prev-type (or (:type prev-slot) :nil)
        new-type (:type new-slot)
        prev-value (:value prev-slot)]

    (case [prev-type new-type]
      ;; nil → nil: no change
      [:nil :nil]
      {:slot new-slot :delta nil}

      ;; nil → single: add
      [:nil :single]
      {:slot new-slot
       :delta {:delta :add :path [slot-index] :value new-result}}

      ;; nil → keyed: add all items (fragment becoming visible)
      [:nil :keyed]
      {:slot new-slot
       :delta {:delta :add-fragment :path [slot-index] :value new-result}}

      ;; single → nil: remove
      [:single :nil]
      {:slot new-slot
       :delta {:delta :remove :path [slot-index] :old-value prev-value}}

      ;; single → single: update if changed
      ;; Compare vnodes semantically:
      ;; - For element vnodes: same tag + same ADDRESS (see below)
      ;;   When unchanged, the child handles its own deltas via discharge-vnode!
      ;; - For text nodes: compare content directly
      ;; - Otherwise: use reference equality
      [:single :single]
      (let [unchanged?
            (cond
              ;; Both are text nodes - compare content
              (and (core/text-node? prev-value) (core/text-node? new-result))
              (= (:content prev-value) (:content new-result))

              ;; Both are element vnodes. Identity IS the address, because that
              ;; is what `discharge-vnode!` binds DOM elements by. A keyed
              ;; element's addr already embeds its key
              ;; (`keyed-child-address(my-addr, key)`), so addr equality implies
              ;; key equality AND structural position.
              ;;
              ;; Comparing keys alone (the old rule) declared a child
              ;; "unchanged" whenever the key matched, emitting no delta on the
              ;; assumption below. That assumption holds only if the child's
              ;; addr is stable — and it is not: two branches of an `if` are
              ;; distinct source locations, hence distinct addrs. The child's
              ;; deltas then targeted an addr with no bound DOM element and
              ;; vanished silently (a self-tracking child spin whose root
              ;; branch flipped would freeze forever).
              ;;
              ;; `:key` on a plain element is a DISAMBIGUATOR, not an identity
              ;; token — see `addressing/keyed-child-address`. Position-
              ;; independent identity is `ifor-each`'s job, and its items travel
              ;; through the `:keyed` slot type, never through here.
              ;;
              ;; DO NOT check (:deltas new-result) - that would cause parent to
              ;; trigger :update which calls render-initial! and bypasses child deltas
              (and (core/vnode? prev-value) (core/vnode? new-result))
              (let [same-tag? (= (:tag prev-value) (:tag new-result))
                    prev-addr (:addr prev-value)
                    new-addr (:addr new-result)
                    same-identity? (if (and prev-addr new-addr)
                                     (= prev-addr new-addr)
                                     ;; Legacy vnodes without addrs: fall back to
                                     ;; the old key/no-key rule.
                                     (let [prev-key (:key prev-value)
                                           new-key (:key new-result)]
                                       (if (and prev-key new-key)
                                         (= prev-key new-key)
                                         (and (nil? prev-key) (nil? new-key)))))]
                (and same-tag? same-identity?))

              ;; Otherwise use reference equality
              :else (= prev-value new-result))]
        (if unchanged?
          {:slot new-slot :delta nil}
          {:slot new-slot
           :delta {:delta :update :path [slot-index]
                   :old-value prev-value :value new-result}}))

      ;; single → keyed: replace with fragment
      [:single :keyed]
      {:slot new-slot
       :delta {:delta :replace-with-fragment :path [slot-index]
               :old-value prev-value :value new-result}}

      ;; keyed → nil: remove all items
      [:keyed :nil]
      {:slot new-slot
       :delta {:delta :remove-fragment :path [slot-index] :old-value prev-value}}

      ;; keyed → single: replace fragment with single
      [:keyed :single]
      {:slot new-slot
       :delta {:delta :replace-fragment-with-single :path [slot-index]
               :old-value prev-value :value new-result}}

      ;; keyed → keyed: propagate fragment's internal deltas
      [:keyed :keyed]
      (let [fragment-deltas (when (keyed-fragment? new-result)
                              (:deltas new-result))]
        {:slot new-slot
         :delta (when (seq fragment-deltas)
                  {:delta :fragment-update :path [slot-index]
                   :deltas fragment-deltas})})

      ;; Fallback: treat as update
      {:slot new-slot
       :delta {:delta :update :path [slot-index]
               :old-value prev-value :value new-result}})))

(defn reconcile-children
  "Reconcile all children against cached slots.

  Args:
    prev-cache - Vector of previous slot entries (or nil)
    new-children - Vector of new child results

  Returns: {:slots <vector-of-slot-entries> :deltas <vector-of-deltas>}"
  [prev-cache new-children]
  (let [prev-cache (or prev-cache [])
        max-slots (max (count prev-cache) (count new-children))
        results (mapv (fn [idx]
                        (let [prev-slot (get prev-cache idx)
                              new-result (get new-children idx)]
                          (reconcile-slot idx prev-slot new-result)))
                      (range max-slots))]
    {:slots (mapv :slot results)
     :deltas (into [] (keep :delta results))}))

;; =============================================================================
;; Flatten Slots to Children
;; =============================================================================

(defn flatten-slot
  "Flatten a slot to its child vnodes.

  Returns: Vector of vnodes (may be empty, single, or multiple)"
  [slot]
  (case (:type slot)
    :nil []
    :single [(:value slot)]
    :keyed (if (keyed-fragment? (:value slot))
             (:items (:value slot))
             (:value slot))
    []))

(defn flatten-slots
  "Flatten all slots to a single children vector.

  This produces the final children for the vnode."
  [slots]
  (into [] (mapcat flatten-slot slots)))

;; =============================================================================
;; Compute Flattened Index
;; =============================================================================

(defn slot-base-index
  "Compute the flattened base index for a slot.

  This is the sum of sizes of all preceding slots."
  [slots slot-index]
  (reduce (fn [acc idx]
            (+ acc (count (flatten-slot (get slots idx)))))
          0
          (range slot-index)))

(defn adjust-delta-paths
  "Adjust delta paths from slot-relative to flattened indices.

  Args:
    slots - Vector of slot entries (for computing base indices)
    deltas - Vector of deltas with slot-relative paths

  Returns: Vector of deltas with absolute flattened indices"
  [slots deltas]
  (mapv (fn [delta]
          (let [slot-idx (first (:path delta))
                base-idx (slot-base-index slots slot-idx)]
            (case (:delta delta)
              ;; Simple deltas: just adjust path
              (:add :remove :update)
              (assoc delta :path [base-idx])

              ;; Fragment deltas: adjust each internal delta's path
              :fragment-update
              (let [internal-deltas (:deltas delta)
                    adjusted-internal (mapv (fn [d]
                                              (update d :path
                                                      (fn [p]
                                                        [(+ base-idx (or (first p) 0))])))
                                            internal-deltas)]
                {:delta :fragment-update
                 :path [slot-idx]
                 :adjusted-deltas adjusted-internal})

              ;; Fragment appears/disappears/replaces wholesale.
              ;;
              ;; These used to fall through UNADJUSTED — and `discharge` then
              ;; used `(first path)` as a DOM child index. But an unadjusted path
              ;; is a SLOT index, and slots do not correspond to children: a :nil
              ;; slot flattens to zero nodes, a :keyed slot to many. So an
              ;; ifor-each appearing after such a sibling inserted its items at
              ;; the WRONG index — e.g. before a preceding element instead of
              ;; after it. Silent, and only visible as a mysterious reordering.
              ;;
              ;; They are child-index deltas exactly like :add/:remove/:update,
              ;; so they need exactly the same slot→flattened conversion.
              (:add-fragment :remove-fragment
                             :replace-with-fragment :replace-fragment-with-single)
              (assoc delta :path [base-idx])

              ;; Anything else: leave alone.
              delta)))
        deltas))

;; =============================================================================
;; KeyedFragment Check (defined here to avoid circular deps)
;; =============================================================================

(defn keyed-fragment?
  "Check if x is a KeyedFragment.

  Note: This checks for the expected structure since the record
  is defined in fragment.cljc which may not be loaded yet."
  [x]
  (and (map? x)
       (contains? x :items)
       (contains? x :deltas)
       (vector? (:items x))))
