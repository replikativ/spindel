(ns examples.block-editor-demo
  "Block editor prototype with fully incremental end-to-end updates.

   Architecture:
   - Blocks stored in DOCUMENT ORDER in the signal (DFS traversal order)
   - All state is on the blocks themselves (:collapsed, :focused)
   - All mutations use d/update-by-key which emits proper :update deltas
   - Interval passed directly to ifor-each for O(delta) DOM updates

   Data model:
   - blocks-signal: DeltaableVector of blocks in document order
   - Each block: {:id :content :parent-id :order :collapsed :focused :hidden}
   - :order is sibling order (for sorting within parent)
   - :collapsed boolean - whether this block's children are hidden
   - :focused boolean - whether this block has focus
   - :hidden boolean - whether this block is hidden (any ancestor is collapsed)
   - Position in vector IS the document order

   Delta flow:
   1. User action → mutation function
   2. Mutation uses d/update-by-key → emits :update delta for changed block
   3. Signal stores delta with new value
   4. track returns Interval with deltas
   5. ifor-each receives Interval, processes deltas incrementally
   6. DOM receives only changed elements"
  (:require [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.browser :as browser]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.foreach]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.signal]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.addressing]
            [org.replikativ.spindel.spin.core]
            [is.simm.partial-cps.async]
            [clojure.string :as str])
  (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                   [org.replikativ.spindel.signal :refer [signal]]
                   [org.replikativ.spindel.dom.elements :as el]
                   [org.replikativ.spindel.dom.foreach :refer [ifor-each]]))

;; =============================================================================
;; State
;; =============================================================================

(defonce runtime (ctx/create-execution-context))

;; Blocks stored in DOCUMENT ORDER (DFS traversal order)
;; All state is on the blocks: :collapsed, :focused
(def blocks-signal (signal runtime (d/deltaable-vector [])))

(defonce id-counter (atom 0))
(defonce render-handle (atom nil))

;; =============================================================================
;; Block Data Structure
;; =============================================================================

;; Each block:
;; {:id         int           ;; Unique ID
;;  :content    string        ;; Text content
;;  :parent-id  int|nil       ;; Parent block ID (nil = root)
;;  :order      number        ;; Order among siblings (fractional for insertions)
;;  :collapsed  boolean       ;; Whether THIS block's children are hidden
;;  :focused    boolean       ;; Whether this block has focus
;;  :hidden     boolean       ;; Whether this block is hidden (ancestor is collapsed)
;; }

(defn make-block
  "Create a new block with given content and parent."
  [content parent-id order & {:keys [collapsed focused hidden] :or {collapsed false focused false hidden false}}]
  (let [id (swap! id-counter inc)]
    {:id id
     :content content
     :parent-id parent-id
     :order order
     :collapsed collapsed
     :focused focused
     :hidden hidden}))

;; =============================================================================
;; Index Building (for efficient lookups)
;; =============================================================================

(defn build-block-index
  "Build id->block index for O(1) lookups."
  [blocks]
  (into {} (map (juxt :id identity)) blocks))

(defn build-children-index
  "Build parent-id->[children] index for tree traversal."
  [blocks]
  (group-by :parent-id blocks))

(defn build-position-index
  "Build id->position index for O(1) position lookups."
  [blocks]
  (into {} (map-indexed (fn [i b] [(:id b) i]) blocks)))

;; =============================================================================
;; Block Tree Operations (read-only, used for computing properties)
;; =============================================================================

(defn get-children
  "Get children of a block, sorted by order."
  [children-index parent-id]
  (vec (sort-by :order (get children-index parent-id []))))

(defn get-siblings
  "Get siblings of a block (including itself)."
  [children-index block]
  (get-children children-index (:parent-id block)))

(defn get-previous-sibling
  "Get the previous sibling of a block."
  [children-index block]
  (let [siblings (get-siblings children-index block)
        idx (d/find-index #(= (:id %) (:id block)) siblings)]
    (when (and idx (pos? idx))
      (nth siblings (dec idx)))))

(defn block-depth
  "Calculate nesting depth of a block."
  [block block-index]
  (loop [depth 0
         current block]
    (if-let [parent-id (:parent-id current)]
      (recur (inc depth) (get block-index parent-id))
      depth)))

(defn has-children?
  "Check if a block has children."
  [block-id children-index]
  (seq (get children-index block-id)))

(defn block-hidden?
  "Check if a block should be hidden (any ancestor is collapsed)."
  [block block-index]
  (loop [current block]
    (if-let [parent-id (:parent-id current)]
      (let [parent (get block-index parent-id)]
        (if (:collapsed parent)
          true
          (recur parent)))
      false)))

;; =============================================================================
;; Block Mutations (maintain document order, emit deltas)
;; =============================================================================

(defn insert-block-at
  "Insert a block at a specific position in the deltaable vector.
   Uses d/insert-at for proper :add delta emission, enabling O(delta) DOM updates."
  [blocks insert-pos new-block]
  (d/insert-at blocks insert-pos new-block))

(defn set-focused-block!
  "Set focus to a specific block, unfocusing any currently focused block.
   Emits :update deltas for both the old and new focused blocks."
  [block-id]
  (swap! blocks-signal
         (fn [blocks]
           (reduce (fn [bs idx]
                     (let [block (nth @bs idx)
                           should-focus (= (:id block) block-id)
                           is-focused (:focused block)]
                       (if (not= should-focus is-focused)
                         (d/update-by-key bs :id (:id block) assoc :focused should-focus)
                         bs)))
                   blocks
                   (range (count @blocks))))))

(defn add-block-after!
  "Add a new block after the given block ID.
   Maintains document order. New block is inserted right after the target block."
  [after-id content]
  (swap! blocks-signal
         (fn [blocks]
           (let [blocks-vec @blocks
                 position-index (build-position-index blocks-vec)
                 children-index (build-children-index blocks-vec)
                 after-pos (get position-index after-id)
                 after-block (nth blocks-vec after-pos)
                 siblings (get-children children-index (:parent-id after-block))
                 after-idx-in-siblings (d/find-index #(= (:id %) after-id) siblings)
                 ;; Compute new order (between after-block and next sibling)
                 new-order (if (< after-idx-in-siblings (dec (count siblings)))
                             (let [next-sib (nth siblings (inc after-idx-in-siblings))]
                               (/ (+ (:order after-block) (:order next-sib)) 2))
                             (inc (:order after-block)))
                 ;; New block starts focused
                 new-block (make-block content (:parent-id after-block) new-order :focused true)
                 ;; Insert right after the target block in document order
                 insert-pos (inc after-pos)
                 ;; First unfocus the old block - iterate over plain vector indices
                 unfocused (reduce (fn [bs idx]
                                     (let [block (nth @bs idx)]
                                       (if (:focused block)
                                         (d/update-by-key bs :id (:id block) assoc :focused false)
                                         bs)))
                                   blocks
                                   (range (count blocks-vec)))
                 ;; Insert the new focused block
                 result (insert-block-at unfocused insert-pos new-block)]
             result))))

(defn delete-block!
  "Delete block and reparent children.
   Emits :update deltas for reparented children, :remove delta for deleted block."
  [block-id]
  (let [blocks-vec @blocks-signal
        position-index (build-position-index blocks-vec)
        children-index (build-children-index blocks-vec)
        block-pos (get position-index block-id)
        block (nth blocks-vec block-pos)
        ;; Find previous block for focus
        prev-block (when (pos? block-pos)
                     (nth blocks-vec (dec block-pos)))
        ;; Children that need reparenting
        child-ids (set (map :id (get children-index block-id)))]
    ;; Reparent children, then remove block, then focus previous
    (swap! blocks-signal
           (fn [blocks]
             (let [;; Update children's parent-id
                   updated (reduce (fn [bs child-id]
                                     (d/update-by-key bs :id child-id
                                                      assoc :parent-id (:parent-id block)))
                                   blocks
                                   child-ids)
                   ;; Remove the block
                   removed (d/filter-vec #(not= (:id %) block-id) updated)]
               ;; Focus previous block if there is one
               (if prev-block
                 (d/update-by-key removed :id (:id prev-block) assoc :focused true)
                 removed))))))

(defn update-block-content!
  "Update content of a block. Emits :update delta."
  [block-id content]
  (swap! blocks-signal d/update-by-key :id block-id assoc :content content))

(defn indent-block!
  "Make block a child of its previous sibling.
   Updates parent-id and order, emits :update delta."
  [block-id]
  (let [blocks-vec @blocks-signal
        children-index (build-children-index blocks-vec)
        position-index (build-position-index blocks-vec)
        block-pos (get position-index block-id)
        block (nth blocks-vec block-pos)
        prev-sibling (get-previous-sibling children-index block)]
    (when prev-sibling
      (let [prev-children (get children-index (:id prev-sibling))
            new-order (if (seq prev-children)
                        (inc (:order (last (sort-by :order prev-children))))
                        0)]
        ;; Update block's parent-id and order - emits :update delta
        (swap! blocks-signal
               d/update-by-key :id block-id
               assoc :parent-id (:id prev-sibling) :order new-order)))))

(defn outdent-block!
  "Make block a sibling of its parent.
   Updates parent-id and order, emits :update delta."
  [block-id]
  (let [blocks-vec @blocks-signal
        position-index (build-position-index blocks-vec)
        children-index (build-children-index blocks-vec)
        block-pos (get position-index block-id)
        block (nth blocks-vec block-pos)
        parent-pos (when (:parent-id block) (get position-index (:parent-id block)))
        parent (when parent-pos (nth blocks-vec parent-pos))]
    (when parent
      (let [parent-siblings (get-children children-index (:parent-id parent))
            parent-idx (d/find-index #(= (:id %) (:id parent)) parent-siblings)
            new-order (if (and parent-idx (< parent-idx (dec (count parent-siblings))))
                        (let [next-uncle (nth parent-siblings (inc parent-idx))]
                          (/ (+ (:order parent) (:order next-uncle)) 2))
                        (inc (:order parent)))]
        ;; Update block's parent-id and order - emits :update delta
        (swap! blocks-signal
               d/update-by-key :id block-id
               assoc :parent-id (:parent-id parent) :order new-order)))))

(defn get-all-descendants
  "Get all descendant IDs of a block (children, grandchildren, etc.)."
  [block-id children-index]
  (loop [result []
         to-visit [block-id]]
    (if (empty? to-visit)
      (rest result)  ; Exclude the block itself
      (let [current-id (first to-visit)
            children (map :id (get children-index current-id []))]
        (recur (conj result current-id)
               (into (rest to-visit) children))))))

(defn toggle-collapse!
  "Toggle collapsed state of a block.
   Also updates :hidden on all descendants so they get re-rendered.
   Emits :update deltas for the block AND all its descendants."
  [block-id]
  (swap! blocks-signal
         (fn [blocks]
           (let [blocks-vec @blocks
                 position-index (build-position-index blocks-vec)
                 children-index (build-children-index blocks-vec)
                 block-pos (get position-index block-id)
                 block (nth blocks-vec block-pos)
                 new-collapsed (not (:collapsed block))
                 ;; Get all descendants that need their :hidden updated
                 descendant-ids (get-all-descendants block-id children-index)
                 ;; First update the collapsed block
                 updated (d/update-by-key blocks :id block-id assoc :collapsed new-collapsed)]
             ;; Then update :hidden on all descendants
             ;; When collapsing, descendants become hidden
             ;; When expanding, descendants become visible (unless another ancestor is collapsed)
             (reduce (fn [bs desc-id]
                       (let [desc-block (get (build-block-index @bs) desc-id)
                             ;; Check if any OTHER ancestor is collapsed
                             other-ancestor-collapsed (block-hidden? desc-block (build-block-index @bs))]
                         (d/update-by-key bs :id desc-id assoc :hidden
                                          (or new-collapsed other-ancestor-collapsed))))
                     updated
                     descendant-ids)))))

(defn focus-block!
  "Focus a specific block, unfocusing any currently focused block."
  [block-id]
  (set-focused-block! block-id))

(defn focus-previous!
  "Focus the previous visible block."
  []
  (let [blocks-vec @blocks-signal
        ;; Find currently focused block
        focused-block (first (filter :focused blocks-vec))
        position-index (build-position-index blocks-vec)
        current-pos (when focused-block (get position-index (:id focused-block)))]
    (when current-pos
      ;; Find previous non-hidden block
      (loop [pos (dec current-pos)]
        (when (>= pos 0)
          (let [block (nth blocks-vec pos)]
            (if (:hidden block)
              (recur (dec pos))
              (set-focused-block! (:id block)))))))))

(defn focus-next!
  "Focus the next visible block."
  []
  (let [blocks-vec @blocks-signal
        ;; Find currently focused block
        focused-block (first (filter :focused blocks-vec))
        position-index (build-position-index blocks-vec)
        current-pos (when focused-block (get position-index (:id focused-block)))]
    (when current-pos
      ;; Find next non-hidden block
      (loop [pos (inc current-pos)]
        (when (< pos (count blocks-vec))
          (let [block (nth blocks-vec pos)]
            (if (:hidden block)
              (recur (inc pos))
              (set-focused-block! (:id block)))))))))

;; =============================================================================
;; Block Rendering
;; =============================================================================

(defn render-block
  "Render a single block.
   All render state comes from the block itself - no closure dependencies."
  [block depth has-children]
  (el/div {:class (str "block"
                       (when (:focused block) " focused")
                       (when (:hidden block) " hidden"))
           :style (str "padding-left: " (* depth 24) "px"
                       (when (:hidden block) "; display: none"))
           :data-id (str (:id block))}
    ;; Collapse/expand toggle
    (if has-children
      (el/span {:class (str "collapse-toggle" (when (:collapsed block) " collapsed"))
                :data-action "toggle"
                :data-id (str (:id block))}
        (if (:collapsed block) "+" "-"))
      (el/span {:class "collapse-placeholder"} " "))
    ;; Content area
    (el/div {:class "block-content"
             :contenteditable "true"
             :data-id (str (:id block))
             :data-action "edit"}
      (:content block))))

;; =============================================================================
;; App Spin
;; =============================================================================

(defn make-app-spin [blocks-sig]
  (spin
    (let [;; Track the blocks signal - get the full interval with deltas
          blocks-iv (track blocks-sig)

          ;; Get current block values for computing derived properties
          all-blocks (:new blocks-iv)

          ;; Build indexes for property computation
          block-index (build-block-index @all-blocks)
          children-index (build-children-index @all-blocks)]

      (el/div {:class "block-editor"}
        (el/div {:class "editor-header"}
          (el/h2 "Spindel Block Editor")
          (el/p {:class "subtitle"} "Fully incremental end-to-end updates"))

        (el/div {:class "blocks-container"}
          ;; Pass the INTERVAL directly to ifor-each
          ;; All state is on blocks (:collapsed, :focused, :hidden)
          ;; so ifor-each correctly re-renders only blocks that changed.
          (ifor-each :id blocks-iv
            (fn [block]
              (let [depth (block-depth block block-index)
                    has-children (has-children? (:id block) children-index)]
                (render-block block depth has-children)))))

        (el/div {:class "editor-footer"}
          (el/p {:class "help-text"}
            "Enter: new block | Backspace (empty): delete | Tab: indent | Shift+Tab: outdent | Up/Down: navigate"))))))

;; =============================================================================
;; Event Handling
;; =============================================================================

(defn sync-block-content-from-dom!
  "Sync block content from DOM element to signal state."
  [target block-id]
  (when (and target block-id)
    (let [content (.-textContent target)]
      (update-block-content! block-id content))))

(defn handle-keydown
  "Handle keyboard events."
  [e]
  (let [target (.-target e)
        block-id (when-let [id (.-id (.-dataset target))]
                   (js/parseInt id))
        key (.-key e)
        shift? (.-shiftKey e)]
    (case key
      "Enter"
      (do
        (.preventDefault e)
        (when block-id
          (sync-block-content-from-dom! target block-id)
          (add-block-after! block-id "")))

      "Backspace"
      (let [content (.-textContent target)]
        (when (and block-id (str/blank? content))
          (.preventDefault e)
          (delete-block! block-id)))

      "Tab"
      (do
        (.preventDefault e)
        (when block-id
          (sync-block-content-from-dom! target block-id)
          (if shift?
            (outdent-block! block-id)
            (indent-block! block-id))))

      "ArrowUp"
      (do
        (.preventDefault e)
        (focus-previous!))

      "ArrowDown"
      (do
        (.preventDefault e)
        (focus-next!))

      nil)))

(defn handle-input [_e]
  nil)

(defn handle-blur
  "Sync content when user leaves a block."
  [e]
  (let [target (.-target e)
        block-id (when-let [id (.-id (.-dataset target))]
                   (js/parseInt id))
        content (.-textContent target)]
    (when block-id
      (update-block-content! block-id content))))

(defn handle-click
  "Handle click events."
  [e]
  (let [target (.-target e)
        action (.-action (.-dataset target))
        block-id (when-let [id (.-id (.-dataset target))]
                   (js/parseInt id))]
    (case action
      "toggle"
      (when block-id
        (toggle-collapse! block-id))

      "edit"
      (when block-id
        (let [blocks-vec @blocks-signal
              block (first (filter #(= (:id %) block-id) blocks-vec))]
          (when (and block (not (:focused block)))
            (focus-block! block-id))))

      (when-let [block-el (.closest target ".block")]
        (when-let [id (.-id (.-dataset block-el))]
          (let [clicked-id (js/parseInt id)
                blocks-vec @blocks-signal
                block (first (filter #(= (:id %) clicked-id) blocks-vec))]
            (when (and block (not (:focused block)))
              (focus-block! clicked-id))))))))

(defn handle-focus
  "Handle focus events."
  [e]
  (let [target (.-target e)]
    (when (= (.-action (.-dataset target)) "edit")
      (when-let [id (.-id (.-dataset target))]
        (let [block-id (js/parseInt id)
              blocks-vec @blocks-signal
              block (first (filter #(= (:id %) block-id) blocks-vec))]
          (when (and block (not (:focused block)))
            (focus-block! block-id)))))))

;; =============================================================================
;; Focus Management
;; =============================================================================

(defonce focus-render-handle (atom nil))

(defn focus-dom-element!
  "Focus the DOM element for a given block ID."
  [block-id]
  (js/setTimeout
    (fn []
      (when-let [el (js/document.querySelector
                      (str ".block-content[data-id=\"" block-id "\"]"))]
        (when (not= el js/document.activeElement)
          (.focus el)
          (let [range (js/document.createRange)
                sel (js/window.getSelection)]
            (.selectNodeContents range el)
            (.collapse range false)
            (.removeAllRanges sel)
            (.addRange sel range)))))
    10))

(defn make-focus-spin
  "Create a spin that tracks blocks and focuses the focused block.
   Uses blocks-signal directly since :focused is now a block property."
  [blocks-sig]
  (spin
    (let [blocks-iv (track blocks-sig)
          all-blocks @(:new blocks-iv)
          focused-block (first (filter :focused all-blocks))]
      (when focused-block
        (focus-dom-element! (:id focused-block)))
      (el/div {:style "display:none"} nil))))

;; =============================================================================
;; Initialization
;; =============================================================================

(defn init-sample-data!
  "Initialize with sample hierarchical blocks in document order."
  []
  (binding [ec/*execution-context* runtime]
    ;; Create blocks - first block starts focused
    (let [block1 (make-block "Welcome to Spindel Block Editor" nil 0 :focused true)
          block2 (make-block "Features" nil 1)
          block2a (make-block "Incremental DOM updates" (:id block2) 0)
          block2b (make-block "Hierarchical structure" (:id block2) 1)
          block2b1 (make-block "Parent/child relationships" (:id block2b) 0)
          block2b2 (make-block "Indent/outdent with Tab" (:id block2b) 1)
          block2c (make-block "Keyboard navigation" (:id block2) 2)
          block3 (make-block "Getting Started" nil 2)
          block3a (make-block "Click on any block to edit" (:id block3) 0)
          block3b (make-block "Press Enter to create new blocks" (:id block3) 1)]

      ;; Store in DOCUMENT ORDER (DFS traversal)
      (reset! blocks-signal
              (d/deltaable-vector [block1           ; Root 1 (focused)
                                   block2           ; Root 2
                                   block2a          ;   Child 2a
                                   block2b          ;   Child 2b
                                   block2b1         ;     Grandchild 2b1
                                   block2b2         ;     Grandchild 2b2
                                   block2c          ;   Child 2c
                                   block3           ; Root 3
                                   block3a          ;   Child 3a
                                   block3b])))))    ;   Child 3b

(defn ^:export init []
  (js/console.log "Initializing Block Editor demo (fully incremental)...")

  (init-sample-data!)

  (let [container (js/document.getElementById "editor-container")
        focus-container (js/document.getElementById "focus-container")
        discharge (browser/make-dom-discharge js/document)]

    (binding [ec/*execution-context* runtime]
      (let [app-spin (make-app-spin blocks-signal)]
        (reset! render-handle
                (render/render-spin! container app-spin discharge))))

    (binding [ec/*execution-context* runtime]
      (let [focus-spin (make-focus-spin blocks-signal)]
        (reset! focus-render-handle
                (render/render-spin! focus-container focus-spin discharge))))

    (.addEventListener container "keydown" (ec/make-handler runtime handle-keydown))
    (.addEventListener container "input" handle-input)
    (.addEventListener container "click" (ec/make-handler runtime handle-click))
    (.addEventListener container "focus" (ec/make-handler runtime handle-focus) true)
    (.addEventListener container "blur" (ec/make-handler runtime handle-blur) true)

    (js/console.log "Block Editor demo initialized!")))
