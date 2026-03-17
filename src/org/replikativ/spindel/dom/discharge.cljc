(ns org.replikativ.spindel.dom.discharge
  "Effect discharge protocol for applying vdom deltas to external targets.

  This namespace defines the protocol for discharging vdom changes to
  real targets (DOM, string for SSR, test mock, etc.).

  **Delta-Direct Rendering:**

  In the new system, deltas flow directly from elements:
  1. Elements produce deltas during slot reconciliation
  2. Deltas are attached to vnodes in :deltas field
  3. Discharge applies deltas without re-diffing
  4. Deltas cleared after discharge

  **Delta Types:**

  From slot reconciliation:
  - :add - Add child at path
  - :remove - Remove child at path
  - :update - Replace child at path
  - :move - Move child from one position to another (reordering)

  From KeyedFragment handling:
  - :add-fragment - Add all items from fragment
  - :remove-fragment - Remove all items from fragment
  - :replace-with-fragment - Replace single with fragment
  - :replace-fragment-with-single - Replace fragment with single
  - :fragment-update - Internal fragment deltas (with adjusted paths)
  - :replace-all - Full collection replacement (fallback)

  **Attribute Deltas:**

  Still come from DeltaableMap on attrs:
  - :add - Add attribute
  - :update - Update attribute value
  - :remove - Remove attribute

  Implementations:
  - DOMDischarge (browser.cljs) - applies to real browser DOM
  - StringDischarge (string.cljc) - renders to HTML string for SSR
  - MockDischarge (for testing) - logs operations"
  (:require [org.replikativ.spindel.dom.core :as core]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.log :as log]))

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

  (set-text-content! [this el text]
    "Set text content of a text node.")

  (get-element [this addr]
    "Get the target element by address keyword (from element map).")

  (set-element! [this addr el]
    "Store element reference by address keyword.")

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
(declare clear-deltas-deep)
(declare call-ref!)
(declare call-refs-on-unmount!)

;; Track vnodes that have been fully rendered via render-initial!
;; These should not have their deltas applied again.
(def ^:dynamic *rendered-vnodes* nil)

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

(defn apply-attr-deltas!
  "Apply all attribute deltas from vnode to element."
  [discharge el vnode]
  (when-let [attrs (:attrs vnode)]
    (when-let [attr-deltas (d/get-deltas attrs)]
      (doseq [delta attr-deltas]
        (apply-attr-delta! discharge el delta)))))

;; =============================================================================
;; Child Delta Application (New Delta-Direct System)
;; =============================================================================

(defn apply-child-delta!
  "Apply a single child delta from slot reconciliation."
  [discharge el delta]
  (case (:delta delta)
    ;; Simple add: render and insert
    ;; IMPORTANT: After render-initial!, mark the vnode subtree as rendered to prevent
    ;; double-application. The vnode may have deltas from element* reconciliation
    ;; against empty cache, but render-initial! already creates all children.
    ;; Without marking, those deltas would be applied again when discharge-vnode!
    ;; processes the child vnodes (since they're in the pre-computed nodes-with-deltas list).
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

    ;; Simple update: render and replace
    :update
    (let [{:keys [path value old-value]} delta
          index (first path)]
      ;; Call ref callbacks with nil on old element before replacing
      (call-refs-on-unmount! old-value)
      (let [child-el (render-initial! discharge value)]
        (when child-el
          (replace-child! discharge el child-el index))))

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

    ;; Unknown delta type - ignore
    nil))

(defn apply-child-deltas!
  "Apply all child deltas from vnode to element.

  Deltas come from two sources:
  1. The :deltas field set by element* during slot reconciliation
  2. The DeltaableVector children (from dom/append-child, dom/update-child, etc.)"
  [discharge el vnode]
  ;; Apply slot reconciliation deltas
  (when-let [deltas (:deltas vnode)]
    (doseq [delta deltas]
      (apply-child-delta! discharge el delta)))
  ;; Apply DeltaableVector children deltas (from direct manipulation)
  (when-let [children (:children vnode)]
    (when-let [child-deltas (d/get-deltas children)]
      (doseq [delta child-deltas]
        (apply-child-delta! discharge el delta)))))

;; =============================================================================
;; VNode Discharge
;; =============================================================================

(defn discharge-vnode!
  "Discharge all deltas from a vnode to the target element.

  Applies:
  1. Attribute deltas (from DeltaableMap)
  2. Child deltas (from slot reconciliation :deltas field)

  Skips vnodes that were already fully rendered via render-initial! during
  this discharge cycle (tracked in *rendered-vnodes*)."
  [discharge vnode]
  (when vnode
    ;; Skip if this vnode was already fully rendered via render-initial!
    ;; This prevents double-application of deltas for newly added elements
    (let [is-rendered? (and *rendered-vnodes* (contains? @*rendered-vnodes* vnode))]
      (log/debug! {:event ::discharge-vnode
                   :data {:tag (:tag vnode)
                          :is-rendered? is-rendered?
                          :has-child-deltas (boolean (seq (:deltas vnode)))
                          :child-delta-count (count (:deltas vnode))
                          :rendered-set-size (when *rendered-vnodes* (count @*rendered-vnodes*))}})
      (when-not is-rendered?
        (let [el (get-element discharge (:addr vnode))]
          (when-not el
            (log/debug! {:event ::element-not-found
                         :data {:addr (:addr vnode) :tag (:tag vnode)
                                :delta-count (count (:deltas vnode))}}))
          (when el
            ;; Apply attribute deltas
            (apply-attr-deltas! discharge el vnode)

            ;; Apply child deltas (from new delta-direct system)
            (apply-child-deltas! discharge el vnode)))))))

;; =============================================================================
;; Tree Walking
;; =============================================================================

(defn collect-nodes-with-deltas
  "Walk vdom tree and collect all nodes that have deltas.

  A node has deltas if:
  - It has attribute deltas (from DeltaableMap)
  - It has child deltas (from :deltas field)"
  [vnode]
  (when vnode
    (let [has-attr-deltas? (and (:attrs vnode) (d/has-deltas? (:attrs vnode)))
          has-child-deltas? (or (seq (:deltas vnode))
                            (and (:children vnode) (d/has-deltas? (:children vnode))))
          has-deltas? (or has-attr-deltas? has-child-deltas?)
          children (when-let [ch (:children vnode)]
                     (if (d/deltaable? ch) @ch ch))
          child-results (mapcat collect-nodes-with-deltas children)]
      (when has-deltas?
        (log/debug! {:event ::collected-node-with-deltas
                     :data {:tag (:tag vnode)
                            :child-delta-count (count (:deltas vnode))
                            :deltas (mapv #(select-keys % [:delta :path]) (:deltas vnode))}}))
      (if has-deltas?
        (cons vnode child-results)
        child-results))))

(defn discharge-all!
  "Discharge all deltas from vdom tree to target.

  1. Collect all nodes with deltas
  2. Apply each node's deltas (skipping those rendered via render-initial!)
  3. Clear deltas for next render cycle

  Uses *rendered-vnodes* dynamic var to track vnodes that have been fully
  rendered during this cycle. This prevents double-application of deltas
  when a parent's :add delta triggers render-initial! for a child that
  also appears in the nodes-with-deltas list.

  Returns the vdom with deltas cleared."
  [discharge vdom]
  (binding [*rendered-vnodes* (atom #{})]
    (let [nodes (collect-nodes-with-deltas vdom)]
      (log/debug! {:event ::discharge-all
                   :data {:nodes-count (count nodes)
                          :nodes-with-deltas (mapv (fn [n] {:tag (:tag n) :deltas (:deltas n)}) nodes)}})
      (doseq [node nodes]
        (discharge-vnode! discharge node))
      (clear-deltas-deep vdom))))

;; =============================================================================
;; Delta Clearing
;; =============================================================================

(defn clear-deltas
  "Clear deltas from a single vnode."
  [vnode]
  (cond-> vnode
    (:attrs vnode) (update :attrs d/clear-deltas)
    (:children vnode) (update :children d/clear-deltas)
    (:deltas vnode) (dissoc :deltas)))

(defn clear-deltas-deep
  "Recursively clear deltas from vnode and all descendants."
  [vnode]
  (cond
    (nil? vnode) nil

    (core/text-node? vnode) vnode

    :else
    (let [cleared (clear-deltas vnode)
          children (:children cleared)]
      (if children
        (let [child-vec (if (d/deltaable? children) @children children)]
          (assoc cleared :children
                 (d/deltaable-vector
                   (mapv clear-deltas-deep child-vec))))
        cleared))))

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
        (log/error! {:event ::ref-callback-error
                     :data {:tag (:tag vnode)
                            :el el
                            :error (str e)}})))))

(defn- call-refs-on-unmount!
  "Recursively call ref callbacks with nil for a vnode and its descendants."
  [vnode]
  (when vnode
    (cond
      (core/text-node? vnode)
      nil  ; Text nodes don't have refs

      (frag/keyed-fragment? vnode)
      (doseq [item (frag/fragment-items vnode)]
        (call-refs-on-unmount! item))

      (core/vnode? vnode)
      (do
        (call-ref! vnode nil)
        (when-let [children (:children vnode)]
          (let [child-vec (if (d/deltaable? children) @children children)]
            (doseq [child child-vec]
              (call-refs-on-unmount! child)))))

      :else nil)))

;; =============================================================================
;; Initial Render (create all elements)
;; =============================================================================

(defn- mark-rendered!
  "Mark a vnode as rendered in *rendered-vnodes* if tracking is active."
  [vnode]
  (when (and *rendered-vnodes* vnode)
    (swap! *rendered-vnodes* conj vnode)))

(defn render-initial!
  "Render entire vdom tree to target for initial mount.

  Creates all elements and stores references.
  Also marks all rendered vnodes in *rendered-vnodes* to prevent
  double-application of deltas during discharge-all!."
  [discharge vnode]
  (cond
    (nil? vnode)
    nil

    (core/text-node? vnode)
    (let [el (create-text! discharge (:content vnode))]
      ;; Text nodes don't have :addr — skip storing ref since they're
      ;; always replaced wholesale and never looked up by address
      (mark-rendered! vnode)
      el)

    (core/fragment? vnode)
    ;; Fragments don't create an element, just render children
    (let [children (when-let [ch (:children vnode)]
                     (if (d/deltaable? ch) @ch ch))]
      (mark-rendered! vnode)
      (mapv #(render-initial! discharge %) children))

    (frag/keyed-fragment? vnode)
    ;; KeyedFragment: render all items
    (do
      (mark-rendered! vnode)
      (mapv #(render-initial! discharge %) (frag/fragment-items vnode)))

    (core/vnode? vnode)
    (let [el (create-element! discharge vnode)
          children (when-let [ch (:children vnode)]
                     (if (d/deltaable? ch) @ch ch))]
      ;; Store element reference by stable address
      (set-element! discharge (:addr vnode) el)
      ;; Mark as rendered to prevent double delta application
      (mark-rendered! vnode)

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

  (set-text-content! [_ el text]
    (swap! log conj {:op :set-text :el el :text text}))

  (get-element [_ addr]
    (get @elements addr))

  (set-element! [_ addr el]
    (swap! elements assoc addr el))

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
