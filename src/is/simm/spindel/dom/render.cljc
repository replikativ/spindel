(ns is.simm.spindel.dom.render
  "Reactive rendering - connects spindel's signal system to DOM.

  **Delta-Direct Rendering (New Model):**

  In the delta-direct model, there is no diffing:
  1. Elements are macros that capture source location
  2. Each element has a stable address (from source-loc + parent + slot)
  3. Elements cache their children by slot position
  4. On re-render, slot reconciliation produces deltas directly
  5. Deltas are discharged to the DOM without re-diffing

  The render! function:
  1. Executes a spin that produces vdom with deltas
  2. Mounts vdom to the DOM container (first render)
  3. Re-executes when tracked signals change
  4. Discharges deltas directly to the DOM (no diffing)

  Usage:
    (render! container
      (spin
        (let [{:keys [new]} (track todos)]
          (el/ul
            (ifor-each :id new
              (fn [todo] (el/li (:text todo))))))))

  The spin re-runs whenever tracked signals change. Element macros
  produce vnodes with deltas attached that are discharged to the DOM."
  (:require [is.simm.spindel.dom.core :as dom]
            [is.simm.spindel.dom.discharge :as disch]
            [is.simm.spindel.spin.protocols :as spin-p]
            [is.simm.spindel.log :as log]))

;; =============================================================================
;; Render State
;; =============================================================================

(defrecord RenderState
  [container       ; DOM container element
   discharge       ; Discharge implementation
   current-vdom    ; Current vdom tree (with deltas cleared)
   mounted?])      ; Whether initial mount has happened

;; Forward declarations
(declare transfer-element-refs!)

;; =============================================================================
;; Render Cycle
;; =============================================================================

(defn initial-mount!
  "Perform initial mount of vdom to container."
  [render-state vdom]
  (let [{:keys [container discharge]} render-state
        ;; Clear any existing content
        _ (when container
            (set! (.-innerHTML container) ""))
        ;; Render initial vdom
        root-el (disch/render-initial! discharge vdom)
        ;; Clear deltas for next render cycle
        cleared-vdom (disch/clear-deltas-deep vdom)]
    ;; Append to container
    (when (and container root-el)
      (.appendChild container root-el))
    ;; Transfer element refs from original vdom to cleared vdom
    ;; This is needed because clear-deltas-deep creates new objects
    ;; but discharge stores refs keyed by object identity
    (transfer-element-refs! discharge vdom cleared-vdom)
    ;; Return updated state with cleared vdom
    (assoc render-state
           :current-vdom cleared-vdom
           :mounted? true)))

(defn update-render!
  "Apply vdom changes to DOM using delta-direct rendering.

  In the new model:
  1. Vnodes arrive with deltas already computed (from element* slot reconciliation)
  2. We collect all nodes with deltas
  3. We discharge deltas directly (no diffing)
  4. We clear deltas for next render cycle

  Uses *rendered-vnodes* to track vnodes that are fully rendered during
  this cycle. When a parent's :add delta triggers render-initial! for a child,
  the child vnode is marked as rendered. If the same child appears in the
  nodes-with-deltas list (because it had deltas from element* reconciliation
  against empty cache), discharge-vnode! will skip it to prevent double-rendering.

  The discharge function handles transferring element references
  from old vdom to new vdom based on stable addresses."
  [render-state new-vdom]
  (let [{:keys [discharge current-vdom]} render-state]
    (if (and current-vdom new-vdom)
      ;; Transfer element references from old vdom to new vdom
      ;; This is needed because discharge stores element refs by vnode object
      (let [;; Transfer root element reference
            root-el (disch/get-element discharge current-vdom)]
        (when root-el
          (disch/set-element! discharge new-vdom root-el))

        ;; Discharge deltas directly - no diffing needed
        ;; The deltas come from element* slot reconciliation
        ;; Bind *rendered-vnodes* to track vnodes rendered via render-initial!
        ;; to prevent double-application of deltas
        (binding [disch/*rendered-vnodes* (atom #{})]
          (let [nodes-with-deltas (disch/collect-nodes-with-deltas new-vdom)]
            (when (seq nodes-with-deltas)
              (log/trace! {:event :render/delta-update
                           :data {:nodes-with-deltas (count nodes-with-deltas)}})
              (doseq [node nodes-with-deltas]
                (disch/discharge-vnode! discharge node)))))

        ;; Clear deltas and transfer refs to cleared vdom
        (let [cleared-vdom (disch/clear-deltas-deep new-vdom)]
          ;; Transfer refs to cleared vdom since clear-deltas-deep creates new objects
          (transfer-element-refs! discharge new-vdom cleared-vdom)
          (assoc render-state :current-vdom cleared-vdom)))

      ;; No current vdom - this shouldn't happen after mount
      render-state)))

;; =============================================================================
;; Element Reference Transfer
;; =============================================================================

(defn- find-matching-old-child
  "Find an old child that matches a new child by key or tag.

  Matching rules:
  1. If both have keys, they must match
  2. If new has no key, match by tag at same position
  3. Text nodes match text nodes"
  [new-child old-children-by-key unkeyed-old-at-index]
  (let [new-key (:key new-child)]
    (cond
      ;; New child has key - look up in keyed map
      new-key
      (get old-children-by-key new-key)

      ;; Text nodes - try positional unkeyed match
      (dom/text-node? new-child)
      (when (and unkeyed-old-at-index (dom/text-node? unkeyed-old-at-index))
        unkeyed-old-at-index)

      ;; Element nodes without key - positional match by tag
      (dom/element-node? new-child)
      (when (and unkeyed-old-at-index
                 (dom/element-node? unkeyed-old-at-index)
                 (nil? (:key unkeyed-old-at-index))
                 (= (:tag new-child) (:tag unkeyed-old-at-index)))
        unkeyed-old-at-index)

      :else nil)))

(defn transfer-element-refs!
  "Transfer element references from old vdom tree to new vdom tree.

  This is needed because:
  1. Discharge stores element refs keyed by vnode object identity
  2. Each render produces new vnode objects
  3. We need to connect new vnodes to their existing DOM elements

  In the delta-direct model, elements have stable addresses, but we
  still need to transfer refs because we use vnode object identity
  for the element map (simpler than maintaining address->element map).

  Handles child count changes by using :key attributes for matching
  when available, falling back to positional matching by tag."
  [discharge old-vdom new-vdom]
  (when (and old-vdom new-vdom)
    (cond
      ;; Both are regular element nodes with same tag
      (and (dom/element-node? old-vdom)
           (dom/element-node? new-vdom)
           (= (:tag old-vdom) (:tag new-vdom)))
      (do
        ;; Transfer element reference
        (when-let [el (disch/get-element discharge old-vdom)]
          (disch/set-element! discharge new-vdom el))
        ;; Recursively transfer children with key-aware matching
        (let [old-children (when-let [ch (:children old-vdom)] @ch)
              new-children (when-let [ch (:children new-vdom)] @ch)
              ;; Build index of keyed old children
              old-by-key (reduce (fn [acc child]
                                   (if-let [k (:key child)]
                                     (assoc acc k child)
                                     acc))
                                 {}
                                 old-children)]
          ;; For each new child, find matching old child
          (doseq [[idx new-child] (map-indexed vector new-children)]
            (when new-child
              (let [unkeyed-old-at-idx (get old-children idx)
                    old-child (find-matching-old-child
                               new-child old-by-key unkeyed-old-at-idx)]
                (when old-child
                  (transfer-element-refs! discharge old-child new-child)))))))

      ;; Both are text nodes - transfer ref
      (and (dom/text-node? old-vdom) (dom/text-node? new-vdom))
      (when-let [el (disch/get-element discharge old-vdom)]
        (disch/set-element! discharge new-vdom el))

      ;; Both are fragments - just recurse on children with key-aware matching
      (and (dom/fragment? old-vdom) (dom/fragment? new-vdom))
      (let [old-children (when-let [ch (:children old-vdom)] @ch)
            new-children (when-let [ch (:children new-vdom)] @ch)
            old-by-key (reduce (fn [acc child]
                                 (if-let [k (:key child)]
                                   (assoc acc k child)
                                   acc))
                               {}
                               old-children)]
        (doseq [[idx new-child] (map-indexed vector new-children)]
          (when new-child
            (let [unkeyed-old-at-idx (get old-children idx)
                  old-child (find-matching-old-child
                             new-child old-by-key unkeyed-old-at-idx)]
              (when old-child
                (transfer-element-refs! discharge old-child new-child))))))

      ;; Types don't match - can't transfer
      :else nil)))

(defn update-render-with-transfer!
  "Update render with element reference transfer.

  This version properly transfers element references before discharge.
  Uses *rendered-vnodes* to prevent double-application of deltas."
  [render-state new-vdom]
  (let [{:keys [discharge current-vdom]} render-state]
    (if (and current-vdom new-vdom)
      (do
        ;; Transfer element references from old to new vdom
        (transfer-element-refs! discharge current-vdom new-vdom)

        ;; Discharge deltas directly
        ;; Bind *rendered-vnodes* to track vnodes rendered via render-initial!
        ;; to prevent double-application of deltas
        (binding [disch/*rendered-vnodes* (atom #{})]
          (let [nodes-with-deltas (disch/collect-nodes-with-deltas new-vdom)]
            (log/debug! {:event ::update-render-with-transfer
                         :data {:nodes-with-deltas-count (count nodes-with-deltas)
                                :nodes-summary (mapv (fn [n] {:tag (:tag n)
                                                              :deltas-count (count (:deltas n))
                                                              :deltas (:deltas n)}) nodes-with-deltas)}})
            (when (seq nodes-with-deltas)
              (doseq [node nodes-with-deltas]
                (disch/discharge-vnode! discharge node)))))

        ;; Clear deltas and transfer refs to cleared vdom
        (let [cleared-vdom (disch/clear-deltas-deep new-vdom)]
          ;; Transfer refs to cleared vdom since clear-deltas-deep creates new objects
          (transfer-element-refs! discharge new-vdom cleared-vdom)
          (assoc render-state :current-vdom cleared-vdom)))

      ;; No current vdom
      render-state)))

;; =============================================================================
;; Render! API
;; =============================================================================

#?(:cljs
   (defn make-render-state
     "Create render state for a container element."
     [container discharge-or-nil]
     (let [discharge (or discharge-or-nil
                         ;; Lazy require to avoid circular deps
                         (let [browser-ns (js/require "is.simm.spindel.dom.browser")]
                           ((.-make-dom-discharge browser-ns)
                            (.-ownerDocument container))))]
       (->RenderState container discharge nil false))))

(defn render-once!
  "Render vdom to container once (non-reactive).

  This is useful for static content or testing."
  [container vdom discharge]
  (let [state (->RenderState container discharge nil false)]
    (initial-mount! state vdom)))

(defn create-render-effect
  "Create a render effect function for use with spin completion callbacks.

  Returns a function that:
  - On first call: mounts vdom to container
  - On subsequent calls: discharges deltas to DOM (no diffing)

  The returned function should be called with the vdom result."
  [container discharge]
  (let [state-atom (atom (->RenderState container discharge nil false))]
    (fn [vdom]
      (when vdom
        (let [state @state-atom
              has-deltas? (seq (:deltas vdom))]
          (log/debug! {:event ::render-effect-callback
                       :data {:mounted? (:mounted? state)
                              :vdom-tag (:tag vdom)
                              :vdom-has-deltas? has-deltas?
                              :vdom-deltas (:deltas vdom)}})
          (if (:mounted? state)
            ;; Update with delta-direct rendering
            (swap! state-atom update-render-with-transfer! vdom)
            ;; Initial mount
            (reset! state-atom (initial-mount! state vdom))))))))

;; =============================================================================
;; Integration with Spin System
;; =============================================================================

(defn render-spin!
  "Execute a spin and render its vdom result.

  The spin should return vdom with deltas (from element macros).
  When tracked signals change, the spin re-executes and the
  deltas are discharged directly to the DOM.

  Returns a map with:
    :stop!    - Function to stop reactive updates
    :state    - Atom containing render state

  Example:
    (render-spin! container
      (spin
        (let [{:keys [new]} (track items)]
          (el/ul
            (ifor-each :id new
              (fn [todo] (el/li (:text todo))))))))
  "
  [container the-spin discharge]
  (let [render-effect (create-render-effect container discharge)
        spin-id (spin-p/spin-id the-spin)]

    (log/debug! {:event :render/start
                 :data {:spin-id spin-id}})

    ;; Execute the spin - it will re-run when signals change
    ;; The completion callback renders the vdom
    (the-spin
      ;; resolve callback
      (fn [vdom]
        (log/trace! {:event :render/vdom-received
                     :data {:spin-id spin-id :has-vdom (some? vdom)}})
        (render-effect vdom))
      ;; reject callback
      (fn [error]
        (log/error! {:event :render/error
                     :data {:spin-id spin-id :error error}})))

    ;; Return control map
    {:spin-id spin-id
     :stop! (fn []
              (log/debug! {:event :render/stop
                           :data {:spin-id spin-id}})
              ;; TODO: Implement cancellation
              nil)}))
