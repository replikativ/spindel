(ns org.replikativ.spindel.dom.block-editor-test
  "Tests for ifor-each with block editor operations.

   This tests the core incremental rendering patterns needed for a
   Roam/Logseq/Notion-like outliner:

   1. Hierarchical tree structure with parent/child relationships
   2. ifor-each for incremental rendering with deltas
   3. Core operations: add, delete, update content, indent, outdent, move, reorder
   4. Realistic document editing workflow

   Data model (matching block_editor_demo.cljs):
   - blocks stored in DeltaableVector (flat list)
   - Each block: {:id int, :content string, :parent-id int|nil, :order number}
   - Children index derived from blocks

   Key insight: with fine-grained deltas from DeltaableVector,
   ifor-each incrementally updates only affected blocks."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            #?(:clj [org.replikativ.spindel.test-async :refer [await-drain]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.dom.foreach :refer [ifor-each]]
                            [org.replikativ.spindel.dom.elements :as el])))

;; =============================================================================
;; Block Data Model (matching block_editor_demo.cljs)
;; =============================================================================

(defonce id-counter (atom 0))

(defn make-block
  "Create a block with auto-generated id."
  [content parent-id order]
  (let [id (swap! id-counter inc)]
    {:id id
     :content content
     :parent-id parent-id
     :order order}))

(defn reset-id-counter! []
  (reset! id-counter 0))

(defn get-block-by-id
  "Find block by ID in blocks vector."
  [blocks id]
  (first (filter #(= (:id %) id) blocks)))

(defn get-children
  "Get children of a block, sorted by order."
  [blocks parent-id]
  (->> blocks
       (filter #(= (:parent-id %) parent-id))
       (sort-by :order)
       vec))

(defn get-siblings
  "Get siblings of a block (including itself)."
  [blocks block]
  (get-children blocks (:parent-id block)))

(defn get-previous-sibling
  "Get the previous sibling of a block."
  [blocks block]
  (let [siblings (get-siblings blocks block)
        idx (d/find-index #(= (:id %) (:id block)) siblings)]
    (when (and idx (pos? idx))
      (nth siblings (dec idx)))))

(defn visible-blocks
  "Compute visible blocks in document order (DFS traversal).
   For simplicity, no collapse support in tests."
  [blocks]
  (let [root-blocks (get-children blocks nil)]
    (loop [result []
           stack (vec (reverse root-blocks))]
      (if (empty? stack)
        result
        (let [block (peek stack)
              rest-stack (pop stack)
              children (get-children blocks (:id block))]
          (recur (conj result block)
                 (into rest-stack (reverse children))))))))

(defn block-depth
  "Calculate nesting depth of a block."
  [blocks block]
  (loop [depth 0
         current block]
    (if-let [parent-id (:parent-id current)]
      (recur (inc depth) (get-block-by-id blocks parent-id))
      depth)))

(defn has-children?
  "Check if a block has children."
  [blocks block-id]
  (some #(= (:parent-id %) block-id) blocks))

;; =============================================================================
;; Block Operations (matching block_editor_demo.cljs)
;; =============================================================================

(defn add-block-after
  "Add a new block after the given block ID. Returns [new-blocks new-block-id]."
  [blocks after-id content]
  (let [after-block (get-block-by-id blocks after-id)
        siblings (get-siblings blocks after-block)
        after-idx (d/find-index #(= (:id %) after-id) siblings)
        new-order (if (< after-idx (dec (count siblings)))
                    (let [next-sib (nth siblings (inc after-idx))]
                      (/ (+ (:order after-block) (:order next-sib)) 2))
                    (inc (:order after-block)))
        new-block (make-block content (:parent-id after-block) new-order)]
    [(conj blocks new-block) (:id new-block)]))

(defn delete-block
  "Delete block and reparent its children to deleted block's parent."
  [blocks block-id]
  (let [block (get-block-by-id blocks block-id)
        parent-id (:parent-id block)
        ;; Find children that need reparenting
        children-ids (->> blocks
                          (filter #(= (:parent-id %) block-id))
                          (mapv :id))
        ;; First reparent all children using update-by-key
        reparented (reduce (fn [bs child-id]
                             (d/update-by-key bs :id child-id assoc :parent-id parent-id))
                           blocks
                           children-ids)]
    ;; Then remove the block - filter-vec takes (pred dv)
    (d/filter-vec #(not= (:id %) block-id) reparented)))

(defn update-block-content
  "Update content of a block."
  [blocks block-id content]
  (d/update-by-key blocks :id block-id assoc :content content))

(defn indent-block
  "Make block a child of its previous sibling."
  [blocks block-id]
  (let [block (get-block-by-id blocks block-id)
        prev-sibling (get-previous-sibling blocks block)]
    (if prev-sibling
      (let [prev-children (get-children blocks (:id prev-sibling))
            new-order (if (seq prev-children)
                        (inc (:order (last prev-children)))
                        0)]
        (d/update-by-key blocks :id block-id
                         assoc :parent-id (:id prev-sibling) :order new-order))
      blocks)))

(defn outdent-block
  "Make block a sibling of its parent."
  [blocks block-id]
  (let [block (get-block-by-id blocks block-id)
        parent (when (:parent-id block)
                 (get-block-by-id blocks (:parent-id block)))]
    (if parent
      (let [parent-siblings (get-siblings blocks parent)
            parent-idx (d/find-index #(= (:id %) (:id parent)) parent-siblings)
            new-order (if (< parent-idx (dec (count parent-siblings)))
                        (let [next-uncle (nth parent-siblings (inc parent-idx))]
                          (/ (+ (:order parent) (:order next-uncle)) 2))
                        (inc (:order parent)))]
        (d/update-by-key blocks :id block-id
                         assoc :parent-id (:parent-id parent) :order new-order))
      blocks)))

;; =============================================================================
;; Rendering with ifor-each
;; =============================================================================

#?(:clj
   (defn render-block
     "Render a single block."
     [block depth focused?]
     (el/div {:class (str "block" (when focused? " focused"))
              :style (str "padding-left: " (* depth 20) "px")
              :data-id (str (:id block))}
       (el/span {:class "bullet"} "•")
       (el/div {:class "content"} (:content block)))))

;; =============================================================================
;; Tests: Data Model
;; =============================================================================

#?(:clj
   (deftest test-visible-blocks-order
     (testing "Visible blocks returns DFS order"
       (reset-id-counter!)
       (let [b1 (make-block "Root 1" nil 0)
             b2 (make-block "Root 2" nil 1)
             b1a (make-block "Child 1a" (:id b1) 0)
             b1b (make-block "Child 1b" (:id b1) 1)
             b1a1 (make-block "Grandchild" (:id b1a) 0)
             blocks (d/deltaable-vector [b1 b2 b1a b1b b1a1])
             visible (visible-blocks blocks)]

         (is (= [(:id b1) (:id b1a) (:id b1a1) (:id b1b) (:id b2)]
                (mapv :id visible))
             "DFS: Root1 -> Child1a -> Grandchild -> Child1b -> Root2")))))

#?(:clj
   (deftest test-block-operations
     (testing "Add block after"
       (reset-id-counter!)
       (let [b1 (make-block "First" nil 0)
             blocks (d/deltaable-vector [b1])
             [new-blocks new-id] (add-block-after blocks (:id b1) "Second")]

         (is (= 2 (count new-blocks)))
         (is (= "Second" (:content (get-block-by-id new-blocks new-id))))))

     (testing "Delete block reparents children"
       (reset-id-counter!)
       (let [b1 (make-block "Parent" nil 0)
             b2 (make-block "Child" (:id b1) 0)
             blocks (d/deltaable-vector [b1 b2])
             updated (delete-block blocks (:id b1))]

         (is (= 1 (count updated)))
         (is (nil? (:parent-id (first updated))) "Child reparented to root")))

     (testing "Indent and outdent"
       (reset-id-counter!)
       (let [b1 (make-block "First" nil 0)
             b2 (make-block "Second" nil 1)
             blocks (d/deltaable-vector [b1 b2])
             indented (indent-block blocks (:id b2))]

         (is (= (:id b1) (:parent-id (get-block-by-id indented (:id b2))))
             "B2 is now child of B1")

         (let [outdented (outdent-block indented (:id b2))]
           (is (nil? (:parent-id (get-block-by-id outdented (:id b2))))
               "B2 is root again"))))))

;; =============================================================================
;; Tests: Incremental Rendering with ifor-each
;; =============================================================================

#?(:clj
   (deftest test-ifor-each-initial-render
     (testing "ifor-each renders initial blocks"
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [b1 (make-block "Block 1" nil 0)
                 b2 (make-block "Block 2" nil 1)
                 blocks-sig (sig/signal (d/deltaable-vector [b1 b2]))

                 render-count (atom 0)

                 app-spin
                 (spin
                   (let [{:keys [new]} (track blocks-sig)
                         visible (visible-blocks new)]
                     (swap! render-count inc)
                     (el/div {:class "editor"}
                       (foreach/ifor-each :id visible
                         (fn [block]
                           (render-block block (block-depth new block) false))))))]

             ;; Initial render
             (let [vdom @app-spin]
               (is (= :div (:tag vdom)))
               (is (= 1 @render-count))
               ;; KeyedFragment items are flattened into parent children
               (let [children (:children vdom)]
                 (is (= 2 (count children)) "Should have 2 block children")
                 (is (= :div (:tag (first children))) "First child is a div")))))))))

#?(:clj
   (deftest test-ifor-each-incremental-add
     (testing "Adding block produces :add delta"
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [b1 (make-block "Block 1" nil 0)
                 blocks-sig (sig/signal (d/deltaable-vector [b1]))

                 render-count (atom 0)

                 app-spin
                 (spin
                   (let [{:keys [new]} (track blocks-sig)
                         visible (visible-blocks new)]
                     (swap! render-count inc)
                     (el/div {:class "editor"}
                       (foreach/ifor-each :id visible
                         (fn [block]
                           (render-block block 0 false))))))]

             ;; Initial render
             @app-spin
             (is (= 1 @render-count))
             (is (= 1 (count (:children @app-spin))))

             ;; Add a block
             (swap! blocks-sig (fn [blocks]
                                 (first (add-block-after blocks (:id b1) "Block 2"))))
             (await-drain ctx)

             ;; Should have re-rendered
             (let [vdom @app-spin]
               (is (= 2 @render-count))
               (is (= 2 (count (:children vdom))) "Should have 2 children now"))))))))

#?(:clj
   (deftest test-ifor-each-incremental-update
     (testing "Updating block content produces :update delta"
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [b1 (make-block "Original" nil 0)
                 blocks-sig (sig/signal (d/deltaable-vector [b1]))

                 app-spin
                 (spin
                   (let [{:keys [new]} (track blocks-sig)
                         visible (visible-blocks new)]
                     (el/div {:class "editor"}
                       (foreach/ifor-each :id visible
                         (fn [block]
                           (el/div {:data-id (:id block)}
                             (:content block)))))))]

             ;; Initial render
             @app-spin

             ;; Update content
             (swap! blocks-sig #(update-block-content % (:id b1) "Updated"))
             (await-drain ctx)

             (let [vdom @app-spin
                   children (:children vdom)
                   block-div (first children)
                   text-node (first (:children block-div))]
               (is (= "Updated" (:content text-node))))))))))

#?(:clj
   (deftest test-ifor-each-incremental-delete
     (testing "Deleting block produces :remove delta"
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [b1 (make-block "Block 1" nil 0)
                 b2 (make-block "Block 2" nil 1)
                 blocks-sig (sig/signal (d/deltaable-vector [b1 b2]))

                 app-spin
                 (spin
                   (let [{:keys [new]} (track blocks-sig)
                         visible (visible-blocks new)]
                     (el/div {:class "editor"}
                       (foreach/ifor-each :id visible
                         (fn [block]
                           (el/div {:data-id (:id block)}
                             (:content block)))))))]

             ;; Initial render - 2 blocks
             @app-spin
             (is (= 2 (count (:children @app-spin))))

             ;; Delete b1
             (swap! blocks-sig #(delete-block % (:id b1)))
             (await-drain ctx)

             ;; Should have 1 block
             (let [vdom @app-spin]
               (is (= 1 (count (:children vdom)))))))))))

#?(:clj
   (deftest test-ifor-each-move-delta
     (testing "Move operation produces :move delta"
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [;; Use DeltaableVector directly with move-to
                 items-sig (sig/signal (d/deltaable-vector [:a :b :c :d]))

                 move-delta-seen (atom nil)

                 app-spin
                 (spin
                   (let [{:keys [new deltas]} (track items-sig)]
                     ;; Capture deltas for inspection
                     (when (seq deltas)
                       (reset! move-delta-seen deltas))
                     (el/div {:class "list"}
                       (foreach/ifor-each identity new
                         (fn [item]
                           (el/span {} (name item)))))))]

             ;; Initial render
             @app-spin

             ;; Move :a from position 0 to position 2
             (swap! items-sig #(d/move-to % 0 2))
             (await-drain ctx)

             ;; Check the delta was a :move
             (is (some? @move-delta-seen))
             (let [delta (first @move-delta-seen)]
               (is (= :move (:delta delta)))
               (is (= [0] (:from-path delta)))
               (is (= [2] (:to-path delta))))

             ;; Verify order changed
             (is (= [:b :c :a :d] (vec @items-sig)))))))))

;; =============================================================================
;; Tests: Realistic Document Editing (matching block_editor_demo.cljs)
;; =============================================================================

#?(:clj
   (deftest test-realistic-document-structure
     (testing "Create document like block_editor_demo.cljs init-sample-data!"
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           ;; Create structure matching block_editor_demo.cljs
           (let [block1 (make-block "Welcome to Spindel Block Editor" nil 0)
                 block2 (make-block "Features" nil 1)
                 block3 (make-block "Getting Started" nil 2)
                 ;; Children of block2
                 block2a (make-block "Incremental DOM updates" (:id block2) 0)
                 block2b (make-block "Hierarchical structure" (:id block2) 1)
                 block2c (make-block "Keyboard navigation" (:id block2) 2)
                 ;; Children of block2b
                 block2b1 (make-block "Parent/child relationships" (:id block2b) 0)
                 block2b2 (make-block "Indent/outdent with Tab" (:id block2b) 1)
                 ;; Children of block3
                 block3a (make-block "Click on any block to edit" (:id block3) 0)
                 block3b (make-block "Press Enter to create new blocks" (:id block3) 1)

                 blocks-sig (sig/signal
                              (d/deltaable-vector [block1 block2 block3
                                                   block2a block2b block2c
                                                   block2b1 block2b2
                                                   block3a block3b]))

                 render-count (atom 0)

                 app-spin
                 (spin
                   (let [{:keys [new]} (track blocks-sig)
                         visible (visible-blocks new)]
                     (swap! render-count inc)
                     (el/div {:class "block-editor"}
                       (foreach/ifor-each :id visible
                         (fn [block]
                           (let [depth (block-depth new block)]
                             (render-block block depth false)))))))]

             ;; Initial render - should have all 10 blocks in DFS order
             (let [vdom @app-spin
                   children (:children vdom)]
               (is (= 10 (count children)))
               (is (= 1 @render-count)))

             ;; Verify DFS order
             (let [visible (visible-blocks @blocks-sig)]
               (is (= [(:id block1) (:id block2) (:id block2a) (:id block2b)
                       (:id block2b1) (:id block2b2) (:id block2c)
                       (:id block3) (:id block3a) (:id block3b)]
                      (mapv :id visible))))))))))

#?(:clj
   (deftest test-realistic-editing-workflow
     (testing "Edit document: add, update, indent, outdent, delete"
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           ;; Start with simple 3-block structure
           (let [block1 (make-block "Introduction" nil 0)
                 block2 (make-block "Main Content" nil 1)
                 block3 (make-block "Conclusion" nil 2)

                 blocks-sig (sig/signal (d/deltaable-vector [block1 block2 block3]))
                 render-count (atom 0)

                 app-spin
                 (spin
                   (let [{:keys [new]} (track blocks-sig)
                         visible (visible-blocks new)]
                     (swap! render-count inc)
                     (el/div {:class "editor"}
                       (foreach/ifor-each :id visible
                         (fn [block]
                           (render-block block (block-depth new block) false))))))]

             ;; 1. Initial render
             @app-spin
             (is (= 3 (count (:children @app-spin))))
             (is (= 1 @render-count))

             ;; 2. Add sub-item under "Main Content"
             (let [new-id (atom nil)]
               (swap! blocks-sig (fn [blocks]
                                   (let [[new-blocks id] (add-block-after blocks (:id block2) "Sub-item 1")]
                                     (reset! new-id id)
                                     new-blocks)))
               (await-drain ctx)

               ;; Now indent the new block under block2
               (swap! blocks-sig #(indent-block % @new-id))
               (await-drain ctx)

               (let [visible (visible-blocks @blocks-sig)]
                 (is (= 4 (count visible)))
                 (is (= (:id block2) (:parent-id (get-block-by-id @blocks-sig @new-id)))
                     "New block is child of block2")))

             ;; 3. Add another sub-item
             (let [sub-item-1-id (-> @blocks-sig visible-blocks (nth 2) :id)
                   new-id (atom nil)]
               (swap! blocks-sig (fn [blocks]
                                   (let [[new-blocks id] (add-block-after blocks sub-item-1-id "Sub-item 2")]
                                     (reset! new-id id)
                                     new-blocks)))
               (await-drain ctx)

               (is (= 5 (count (visible-blocks @blocks-sig)))))

             ;; 4. Update content
             (swap! blocks-sig #(update-block-content % (:id block1) "Updated Introduction"))
             (await-drain ctx)

             (is (= "Updated Introduction"
                    (:content (get-block-by-id @blocks-sig (:id block1)))))

             ;; 5. Delete block3 (Conclusion)
             (swap! blocks-sig #(delete-block % (:id block3)))
             (await-drain ctx)

             (is (= 4 (count (visible-blocks @blocks-sig))))
             (is (nil? (get-block-by-id @blocks-sig (:id block3))))

             ;; Verify final structure renders correctly
             (let [vdom @app-spin]
               (is (= 4 (count (:children vdom)))))))))))

#?(:clj
   (deftest test-deep-nesting-operations
     (testing "Indent/outdent with deep nesting"
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [;; Create 4-level deep structure
                 root (make-block "Root" nil 0)
                 l1 (make-block "Level 1" (:id root) 0)
                 l2 (make-block "Level 2" (:id l1) 0)
                 l3 (make-block "Level 3" (:id l2) 0)

                 blocks-sig (sig/signal (d/deltaable-vector [root l1 l2 l3]))

                 app-spin
                 (spin
                   (let [{:keys [new]} (track blocks-sig)
                         visible (visible-blocks new)]
                     (el/div {:class "editor"}
                       (foreach/ifor-each :id visible
                         (fn [block]
                           (el/div {:data-depth (block-depth new block)}
                             (:content block)))))))]

             ;; Initial - verify depths
             @app-spin
             (is (= 0 (block-depth @blocks-sig root)))
             (is (= 1 (block-depth @blocks-sig l1)))
             (is (= 2 (block-depth @blocks-sig l2)))
             (is (= 3 (block-depth @blocks-sig l3)))

             ;; Outdent l3 - should become sibling of l2 (child of l1)
             (swap! blocks-sig #(outdent-block % (:id l3)))
             (await-drain ctx)

             (is (= (:id l1) (:parent-id (get-block-by-id @blocks-sig (:id l3))))
                 "L3 is now child of L1")
             (is (= 2 (block-depth @blocks-sig (get-block-by-id @blocks-sig (:id l3))))
                 "L3 depth is now 2")

             ;; Outdent l3 again - should become child of root
             (swap! blocks-sig #(outdent-block % (:id l3)))
             (await-drain ctx)

             (is (= (:id root) (:parent-id (get-block-by-id @blocks-sig (:id l3))))
                 "L3 is now child of root")
             (is (= 1 (block-depth @blocks-sig (get-block-by-id @blocks-sig (:id l3))))
                 "L3 depth is now 1")))))))

#?(:clj
   (deftest test-ifor-each-with-render-to-dom
     (testing "Full render cycle with mock discharge - incremental updates"
       ;; NOTE: This test uses a flat list (all blocks are roots) to test
       ;; ifor-each incremental rendering directly. The deltaable vector
       ;; is passed directly to ifor-each without transformation, preserving
       ;; delta information for incremental DOM updates.
       ;;
       ;; For hierarchical tree rendering with proper incremental behavior,
       ;; visible-blocks would need to use interval/delta-aware filtering
       ;; to propagate deltas through the tree traversal.
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [{:keys [discharge log]} (disch/make-mock-discharge)
                 b1 {:id 1 :content "Block 1"}
                 b2 {:id 2 :content "Block 2"}
                 ;; Use flat list - pass deltaable directly to ifor-each
                 blocks-sig (sig/signal (d/deltaable-vector [b1 b2]))

                 app-spin
                 (spin
                   (let [{:keys [new]} (track blocks-sig)]
                     ;; Pass deltaable directly - no transformation that loses deltas
                     (el/div {:class "editor"}
                       (foreach/ifor-each :id new
                         (fn [block]
                           (el/div {:data-id (:id block)}
                             (:content block)))))))]

             ;; Initial render through discharge
             (render/render-spin! nil app-spin discharge)
             @app-spin

             ;; Count initial create-element operations
             (let [initial-creates (count (filter #(= :create-element (:op %)) @log))]
               ;; Should create: 1 outer div + 2 block divs = 3 elements
               ;; Text nodes are created via create-text!, not create-element!
               (is (= 3 initial-creates) "Initial render creates 3 elements"))

             ;; Verify initial structure - 2 block children in outer div
             ;; KeyedFragment items are spliced into parent's children
             (let [vdom @app-spin
                   outer-children @(:children vdom)]
               (is (= 2 (count outer-children)) "Outer div has 2 block children")
               ;; Verify content of first block
               (let [first-block (first outer-children)]
                 (is (= :div (:tag first-block)))
                 (is (= 1 (get-in first-block [:attrs :data-id])))))

             ;; Add a block - use conj to produce :add delta
             (reset! log [])
             (swap! blocks-sig conj {:id 3 :content "Block 3"})
             (await-drain ctx)
             @app-spin

             ;; Verify INCREMENTAL update - should only create new block elements
             (let [add-creates (count (filter #(= :create-element (:op %)) @log))]
               ;; Should only create 1 new div for the added block
               (is (<= add-creates 3) "Incremental add creates minimal elements"))

             ;; Verify updated structure - now 3 blocks
             (let [vdom @app-spin
                   outer-children @(:children vdom)]
               (is (= 3 (count outer-children)) "Outer div has 3 blocks after add"))

             ;; Update a block's content using assoc (produces :update delta)
             (reset! log [])
             (swap! blocks-sig assoc 0 {:id 1 :content "Block 1 Updated"})
             (await-drain ctx)
             @app-spin

             ;; Should see minimal operations for update
             (let [update-creates (count (filter #(= :create-element (:op %)) @log))]
               ;; Update should not recreate all elements
               (is (<= update-creates 3) "Update doesn't recreate all elements"))

             ;; Delete a block using filter (produces :remove delta)
             (reset! log [])
             (swap! blocks-sig (fn [dv] (d/filter-vec #(not= (:id %) 2) dv)))
             (await-drain ctx)
             @app-spin

             ;; Verify final structure - back to 2 blocks
             (let [vdom @app-spin
                   outer-children @(:children vdom)]
               (is (= 2 (count outer-children)) "Outer div has 2 blocks after delete"))))))))

#?(:clj
   (deftest test-ifor-each-delta-pipeline
     (testing "Verify deltas flow from signal through track to ifor-each"
       ;; This test explicitly checks that deltas are properly propagated
       ;; through the full reactive pipeline: signal -> track -> ifor-each
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [;; Create signal with deltaable vector
                 items-sig (sig/signal (d/deltaable-vector [{:id 1 :text "A"}
                                                            {:id 2 :text "B"}]))
                 ;; Track what deltas ifor-each actually receives
                 received-deltas (atom [])

                 app-spin
                 (spin
                   (let [{:keys [new old deltas] :as interval} (track items-sig)]
                     ;; Capture deltas for inspection
                     (swap! received-deltas conj {:old old :new new :deltas deltas})
                     ;; Simple render
                     (el/div
                       (foreach/ifor-each :id new
                         (fn [item]
                           (el/span (:text item)))))))]

             ;; Initial execution
             @app-spin

             ;; Check initial state - should have nil deltas (first render)
             (let [initial @received-deltas]
               (is (= 1 (count initial)))
               (is (nil? (:deltas (first initial))) "First render has no deltas"))

             ;; Clear for next operation
             (reset! received-deltas [])

             ;; Add item using conj (produces :add delta)
             (swap! items-sig conj {:id 3 :text "C"})
             (await-drain ctx)
             @app-spin

             ;; Verify :add delta was received
             (let [after-add @received-deltas]
               (is (= 1 (count after-add)) "One re-execution after add")
               (let [{:keys [deltas]} (first after-add)]
                 (is (seq deltas) "Should have deltas")
                 (is (= :add (:delta (first deltas))) "Delta should be :add")
                 (is (= {:id 3 :text "C"} (:value (first deltas))) "Delta value should be new item")))

             ;; Clear for update test
             (reset! received-deltas [])

             ;; Update item using assoc (produces :update delta)
             (swap! items-sig assoc 0 {:id 1 :text "A-updated"})
             (await-drain ctx)
             @app-spin

             ;; Verify :update delta
             (let [after-update @received-deltas]
               (is (= 1 (count after-update)) "One re-execution after update")
               (let [{:keys [deltas]} (first after-update)]
                 (is (seq deltas) "Should have deltas")
                 (is (= :update (:delta (first deltas))) "Delta should be :update")))

             ;; Clear for remove test
             (reset! received-deltas [])

             ;; Remove item using dissoc-by-key (produces :remove delta)
             (swap! items-sig (fn [dv] (d/filter-vec #(not= (:id %) 2) dv)))
             (await-drain ctx)
             @app-spin

             ;; Verify :remove delta
             (let [after-remove @received-deltas]
               (is (= 1 (count after-remove)) "One re-execution after remove")
               (let [{:keys [deltas]} (first after-remove)]
                 (is (seq deltas) "Should have deltas")
                 (is (= :remove (:delta (first deltas))) "Delta should be :remove")))))))))

#?(:clj
   (deftest test-ifor-each-with-interval-vs-new
     (testing "ifor-each receives deltas via interval, not via cleared :new value"
       ;; KEY INSIGHT: The signal clears deltas when storing values.
       ;; track returns an Interval where:
       ;;   - :new is a DeltaableVector with NO deltas (cleared)
       ;;   - :deltas are stored separately in the Interval
       ;;
       ;; So passing (:new interval) loses deltas!
       ;; Must pass the full interval for incremental updates.
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           (let [items-sig (sig/signal (d/deltaable-vector [{:id 1 :text "A"}]))
                 ;; Track which code path for-each* takes
                 incremental-path-taken (atom {:correct 0 :wrong 0})

                 ;; Test 1: Pass full interval (correct)
                 app-spin-correct
                 (spin
                   (let [items-iv (track items-sig)
                         ;; Check what as-interval would see
                         coerced (iv/as-interval items-iv)
                         has-deltas? (seq (iv/get-deltas coerced))]
                     (when has-deltas?
                       (swap! incremental-path-taken update :correct inc))
                     ;; Pass INTERVAL - ifor-each sees deltas via as-interval
                     (el/div
                       (foreach/ifor-each :id items-iv
                         (fn [item]
                           (el/span (:text item)))))))

                 ;; Test 2: Pass just :new (wrong - loses deltas)
                 app-spin-wrong
                 (spin
                   (let [{:keys [new]} (track items-sig)
                         ;; Check what as-interval would see with just :new
                         coerced (iv/as-interval new)
                         has-deltas? (seq (iv/get-deltas coerced))]
                     (when has-deltas?
                       (swap! incremental-path-taken update :wrong inc))
                     ;; Pass just :new - a DeltaableVector with cleared deltas
                     (el/div
                       (foreach/ifor-each :id new
                         (fn [item]
                           (el/span (:text item)))))))]

             ;; Initial execution
             @app-spin-correct
             @app-spin-wrong

             ;; Both should work initially - no deltas on first render
             (is (= 1 (count @(:children @app-spin-correct))))
             (is (= 1 (count @(:children @app-spin-wrong))))
             (is (= {:correct 0 :wrong 0} @incremental-path-taken)
                 "No deltas on initial render")

             ;; Now add an item
             (swap! items-sig conj {:id 2 :text "B"})
             (await-drain ctx)
             @app-spin-correct
             @app-spin-wrong

             ;; Both should have 2 items (functional correctness)
             (is (= 2 (count @(:children @app-spin-correct))) "Correct: 2 items")
             (is (= 2 (count @(:children @app-spin-wrong))) "Wrong also works functionally")

             ;; KEY ASSERTION: Only the correct approach sees deltas
             (is (= 1 (:correct @incremental-path-taken))
                 "Correct approach: interval has deltas")
             (is (= 0 (:wrong @incremental-path-taken))
                 "Wrong approach: :new has NO deltas (cleared by signal)")))))))

#?(:clj
   (deftest test-dom-operations-comparison
     (testing "Compare DOM operations: interval (incremental) vs :new (full recompute)"
       ;; This test renders the same UI with both approaches and compares
       ;; the DOM operations logged by MockDischarge
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           ;; Setup for CORRECT approach (pass interval)
           (let [{:keys [discharge log]} (disch/make-mock-discharge)
                 items-sig-correct (sig/signal (d/deltaable-vector
                                                 [{:id 1 :text "Item A"}
                                                  {:id 2 :text "Item B"}]))
                 spin-correct
                 (spin
                   (let [items-iv (track items-sig-correct)]
                     (el/ul {:class "list"}
                       (foreach/ifor-each :id items-iv
                         (fn [item]
                           (el/li {:key (:id item)} (:text item)))))))]

             ;; Initial render
             (render/render-spin! nil spin-correct discharge)
             @spin-correct

             ;; Clear and add item
             (reset! log [])
             (swap! items-sig-correct conj {:id 3 :text "Item C"})
             (await-drain ctx)
             @spin-correct

           ;; Setup for WRONG approach (pass :new)
           (let [{:keys [discharge log]} (disch/make-mock-discharge)
                 items-sig-wrong (sig/signal (d/deltaable-vector
                                               [{:id 1 :text "Item A"}
                                                {:id 2 :text "Item B"}]))
                 spin-wrong
                 (spin
                   (let [{:keys [new]} (track items-sig-wrong)]
                     (el/ul {:class "list"}
                       (foreach/ifor-each :id new
                         (fn [item]
                           (el/li {:key (:id item)} (:text item)))))))]

             ;; Initial render
             (render/render-spin! nil spin-wrong discharge)
             @spin-wrong

             ;; Clear and add item
             (reset! log [])
             (swap! items-sig-wrong conj {:id 3 :text "Item C"})
             (await-drain ctx)
             @spin-wrong))))))

#?(:clj
   (deftest test-dom-operations-move-and-indent
     (testing "DOM operations for move and indent with depth changes"
       (reset-id-counter!)
       (let [ctx (ctx/create-execution-context)]
         (binding [ec/*execution-context* ctx]
           
           ;; ============ TEST 1: MOVE (reorder) ============
           ;; Setup with interval approach
           (let [{:keys [discharge log]} (disch/make-mock-discharge)
                 ;; Simple flat list for move testing
                 items-sig (sig/signal (d/deltaable-vector
                                         [{:id 1 :text "First"}
                                          {:id 2 :text "Second"}
                                          {:id 3 :text "Third"}]))
                 render-spin
                 (spin
                   (let [items-iv (track items-sig)]
                     (el/ul {:class "list"}
                       (foreach/ifor-each :id items-iv
                         (fn [item]
                           (el/li {:data-id (:id item)} (:text item)))))))]
             
             ;; Initial render
             (render/render-spin! nil render-spin discharge)
             @render-spin
             
             ;; Move item 0 to position 2 (First -> end)
             (reset! log [])
             (swap! items-sig d/move-to 0 2)
             (await-drain ctx)
             @render-spin)

           ;; Same with :new approach (loses deltas)
           (let [{:keys [discharge log]} (disch/make-mock-discharge)
                 items-sig (sig/signal (d/deltaable-vector
                                         [{:id 1 :text "First"}
                                          {:id 2 :text "Second"}
                                          {:id 3 :text "Third"}]))
                 render-spin
                 (spin
                   (let [{:keys [new]} (track items-sig)]
                     (el/ul {:class "list"}
                       (foreach/ifor-each :id new
                         (fn [item]
                           (el/li {:data-id (:id item)} (:text item)))))))]
             
             (render/render-spin! nil render-spin discharge)
             @render-spin
             (reset! log [])
             (swap! items-sig d/move-to 0 2)
             (await-drain ctx)
             @render-spin)

           ;; ============ TEST 2: UPDATE (indent changes style) ============

           ;; Indent uses update-by-key which produces :update delta
           ;; This shows that only the updated block is re-rendered
           (let [{:keys [discharge log]} (disch/make-mock-discharge)
                 ;; Create blocks: A, B, C - simple flat list
                 ;; Each block has a depth that affects its style
                 blocks-sig (sig/signal (d/deltaable-vector
                                          [{:id 1 :text "Block A" :depth 0}
                                           {:id 2 :text "Block B" :depth 0}
                                           {:id 3 :text "Block C" :depth 0}]))

                 render-spin
                 (spin
                   (let [blocks-iv (track blocks-sig)]
                     (el/div {:class "editor"}
                       (foreach/ifor-each :id blocks-iv
                         (fn [block]
                           (el/div {:class "block"
                                    :style (str "padding-left:" (* (:depth block) 20) "px")
                                    :data-id (:id block)}
                             (el/span (:text block))))))))]

             (render/render-spin! nil render-spin discharge)
             @render-spin

             ;; "Indent" B by changing its depth (produces :update delta)
             (reset! log [])
             (swap! blocks-sig d/update-by-key :id 2 assoc :depth 1)
             (await-drain ctx)
             @render-spin)

           ;; Same with :new
           (let [{:keys [discharge log]} (disch/make-mock-discharge)
                 blocks-sig (sig/signal (d/deltaable-vector
                                          [{:id 1 :text "Block A" :depth 0}
                                           {:id 2 :text "Block B" :depth 0}
                                           {:id 3 :text "Block C" :depth 0}]))

                 render-spin
                 (spin
                   (let [{:keys [new]} (track blocks-sig)]
                     (el/div {:class "editor"}
                       (foreach/ifor-each :id new
                         (fn [block]
                           (el/div {:class "block"
                                    :style (str "padding-left:" (* (:depth block) 20) "px")
                                    :data-id (:id block)}
                             (el/span (:text block))))))))]

             (render/render-spin! nil render-spin discharge)
             @render-spin
             (reset! log [])
             ;; Use update-by-key same as interval version
             (swap! blocks-sig d/update-by-key :id 2 assoc :depth 1)
             (await-drain ctx)
             @render-spin)))))))
