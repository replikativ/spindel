(ns org.replikativ.spindel.v2.port.reactive-tree-test
  (:refer-clojure :exclude [await atom])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin await track atom]]
            [org.replikativ.spindel.v2.combinators :as comb :refer [parallel]]
            [org.replikativ.spindel.v2.port.support :refer
             [checking vworld with-world outcome check-result observed-value wait-until required-api]]))

(use-fixtures :each checking)

(defn make-block
  "Create a block with id, parent, order, and content."
  [id parent order content]
  {:block/id id
   :block/parent parent  ; nil for root blocks
   :block/order order
   :block/content content})

(defn blocks->children-index
  "Build children-by-parent index from blocks map.
   Returns {parent-id -> [child-ids sorted by order]}"
  [blocks-map]
  (->> (vals blocks-map)
       (group-by :block/parent)
       (reduce-kv
        (fn [acc parent-id children]
          (assoc acc parent-id
                 (->> children
                      (sort-by :block/order)
                      (mapv :block/id))))
        {})))

(deftest test-index-signal-from-blocks
  (testing "Index signal tracks children-by-parent derived from blocks signal"
    (let [ctx (vworld)]
      (try
        (binding [v2/*world* ctx]
          (let [;; Layer 1: Source data
                blocks-sig (v2/signal
                            {:b1 (make-block :b1 nil 0 "Block 1")
                             :b2 (make-block :b2 nil 1 "Block 2")
                             :b3 (make-block :b3 :b1 0 "Child of B1")})

                ;; Layer 2: Derived index - spin that tracks blocks and maintains index
                ;; Uses runtime atom for internal bookkeeping (per user guidance)
                index-atom (atom {})

                index-maintainer
                (spin
                 (let [{:keys [new]} (track blocks-sig)
                       new-index (blocks->children-index new)]
                   (reset! index-atom new-index)
                   new-index))

                ;; Track how many times index was computed
                index-compute-count (atom 0)

                ;; Consumer spin that awaits the index
                consumer
                (spin
                 (let [index (await index-maintainer)]
                   (swap! index-compute-count inc)
                   index))]

            ;; Initial execution
            (let [result (observed-value consumer)]
              (is (= {nil [:b1 :b2]
                      :b1 [:b3]}
                     result)
                  "Initial index has root children and b1's child")
              (is (= 1 @index-compute-count)))

            ;; Add a new block under b2
            (swap! blocks-sig assoc :b4 (make-block :b4 :b2 0 "Child of B2"))

            (let [result (observed-value consumer)]
              (is (= {nil [:b1 :b2]
                      :b1 [:b3]
                      :b2 [:b4]}
                     result)
                  "Index updated with new child under b2")
              (is (= 2 @index-compute-count) "Consumer re-executed"))))
        (finally
          (v2/release-world! ctx))))))

(deftest test-per-node-reactive-rendering
  (testing "Each node's render spin tracks only its own data"
    (let [ctx (vworld)]
      (try
        (binding [v2/*world* ctx]
          (let [;; Source data
                blocks-sig (v2/signal
                            {:b1 (make-block :b1 nil 0 "Block 1")
                             :b2 (make-block :b2 nil 1 "Block 2")})

                ;; Track render counts per block
                b1-render-count (atom 0)
                b2-render-count (atom 0)

                ;; Simulated render function (returns virtual representation)
                render-block (fn [block-id render-count-atom]
                               (spin
                                (let [{:keys [new]} (track blocks-sig)
                                      block (get new block-id)]
                                  (swap! render-count-atom inc)
                                   ;; Return "vnode" (just data in this test)
                                  {:tag :div
                                   :content (:block/content block)})))

                ;; Create render spins for each block
                b1-render (render-block :b1 b1-render-count)
                b2-render (render-block :b2 b2-render-count)

                ;; Aggregate renders (like parallel would)
                all-renders
                (spin
                 (await (parallel b1-render b2-render)))]

            ;; Initial render
            (let [[r1 r2] (observed-value all-renders)]
              (is (= {:tag :div :content "Block 1"} r1))
              (is (= {:tag :div :content "Block 2"} r2))
              (is (= 1 @b1-render-count))
              (is (= 1 @b2-render-count)))

            ;; Update only b1's content
            (swap! blocks-sig update :b1 assoc :block/content "Updated B1")

            (let [[r1 r2] (observed-value all-renders)]
              (is (= {:tag :div :content "Updated B1"} r1))
              (is (= {:tag :div :content "Block 2"} r2))
              ;; Both re-rendered because they both track blocks-sig
              ;; This is the limitation of coarse-grained signals
              (is (= 2 @b1-render-count))
              (is (= 2 @b2-render-count)))))
        (finally
          (v2/release-world! ctx))))))

(deftest test-fine-grained-block-signals
  (testing "Per-block signals enable truly independent re-renders"
    (let [ctx (vworld)]
      (try
        (binding [v2/*world* ctx]
          (let [;; Per-block signals (fine-grained)
                b1-sig (v2/signal (make-block :b1 nil 0 "Block 1"))
                b2-sig (v2/signal (make-block :b2 nil 1 "Block 2"))

                ;; Track render counts
                b1-render-count (atom 0)
                b2-render-count (atom 0)

                ;; Each spin tracks only its own signal
                b1-render
                (spin
                 (let [{:keys [new]} (track b1-sig)]
                   (swap! b1-render-count inc)
                   {:tag :div :content (:block/content new)}))

                b2-render
                (spin
                 (let [{:keys [new]} (track b2-sig)]
                   (swap! b2-render-count inc)
                   {:tag :div :content (:block/content new)}))

                all-renders
                (spin
                 (await (parallel b1-render b2-render)))]

            ;; Initial render
            (observed-value all-renders)
            (is (= 1 @b1-render-count))
            (is (= 1 @b2-render-count))

            ;; Update only b1
            (swap! b1-sig assoc :block/content "Updated B1")

            (let [[r1 r2] (observed-value all-renders)]
              (is (= {:tag :div :content "Updated B1"} r1))
              (is (= {:tag :div :content "Block 2"} r2))
              ;; Only b1 re-rendered!
              (is (= 2 @b1-render-count) "B1 re-rendered")
              (is (= 1 @b2-render-count) "B2 did NOT re-render"))))
        (finally
          (v2/release-world! ctx))))))

(deftest test-move-updates-two-parents
  (testing "Moving a block updates children lists of both old and new parent"
    (let [ctx (vworld)]
      (try
        (binding [v2/*world* ctx]
          (let [;; Initial: b3 is child of b1
                blocks-sig (v2/signal
                            {:b1 (make-block :b1 nil 0 "Parent 1")
                             :b2 (make-block :b2 nil 1 "Parent 2")
                             :b3 (make-block :b3 :b1 0 "Child")})

                ;; Index maintainer
                index-atom (atom {})
                index-maintainer
                (spin
                 (let [{:keys [new]} (track blocks-sig)
                       new-index (blocks->children-index new)]
                   (reset! index-atom new-index)
                   new-index))

                ;; Track re-renders per parent's children list
                b1-children-render-count (atom 0)
                b2-children-render-count (atom 0)

                ;; Each parent has a spin that renders its children
                b1-children-render
                (spin
                 (let [index (await index-maintainer)
                       children (get index :b1 [])]
                   (swap! b1-children-render-count inc)
                   {:parent :b1 :children children}))

                b2-children-render
                (spin
                 (let [index (await index-maintainer)
                       children (get index :b2 [])]
                   (swap! b2-children-render-count inc)
                   {:parent :b2 :children children}))]

            ;; Initial state
            (observed-value b1-children-render)
            (observed-value b2-children-render)
            (is (= [:b3] (get @index-atom :b1)) "B3 starts under B1")
            (is (= nil (get @index-atom :b2)) "B2 has no children initially")

            ;; Move b3 from b1 to b2
            (swap! blocks-sig update :b3 assoc :block/parent :b2)

;; Force deref to trigger any pending completions
            (observed-value b1-children-render)
            (observed-value b2-children-render)

            (is (= [] (get @index-atom :b1 [])) "B1 now has no children")
            (is (= [:b3] (get @index-atom :b2)) "B2 now has B3")

            ;; Both parent renders should have re-executed
            (is (= 2 @b1-children-render-count) "B1 children re-rendered")
            (is (= 2 @b2-children-render-count) "B2 children re-rendered")))
        (finally
          (v2/release-world! ctx))))))

(deftest test-structural-changes-pattern
  (testing "Pattern for handling structural changes (add/remove/reorder)"
    (let [ctx (vworld)]
      (try
        (binding [v2/*world* ctx]
          (let [;; Children list signal for one parent
                children-sig (v2/signal [:c1 :c2 :c3])

                render-counts (atom {:c1 0 :c2 0 :c3 0 :c4 0})

                ;; Track renders per child
                make-child-render (fn [child-id]
                                    (spin
                                     (let [{:keys [new]} (track children-sig)
                                            ;; Check if we're still in the list
                                           exists? (some #{child-id} new)]
                                       (when exists?
                                         (swap! render-counts update child-id inc))
                                       {:id child-id :exists? exists?})))

                ;; Create initial child renders
                c1-render (make-child-render :c1)
                c2-render (make-child-render :c2)
                c3-render (make-child-render :c3)]

            ;; Initial render
            (observed-value c1-render)
            (observed-value c2-render)
            (observed-value c3-render)
            (is (= {:c1 1 :c2 1 :c3 1 :c4 0} @render-counts))

            ;; Remove c2 from list
            (reset! children-sig [:c1 :c3])

;; All spins that track children-sig re-execute
            ;; but c2 sees it doesn't exist anymore
            (is (= {:c1 2 :c2 1 :c3 2 :c4 0} @render-counts)
                "C1 and C3 re-rendered, C2 didn't increment because exists?=false")))
        (finally
          (v2/release-world! ctx))))))

(deftest test-hierarchical-tree-rendering
  (testing "Recursive tree structure with nested spins"
    (let [ctx (vworld)]
      (try
        (binding [v2/*world* ctx]
          (let [;; Tree structure:
                ;; root
                ;; ├── a
                ;; │   └── a1
                ;; └── b
                blocks-sig (v2/signal
                            {:root (make-block :root nil 0 "Root")
                             :a (make-block :a :root 0 "A")
                             :a1 (make-block :a1 :a 0 "A1")
                             :b (make-block :b :root 1 "B")})

                ;; Index
                index-atom (atom {})
                index-maintainer
                (spin
                 (let [{:keys [new]} (track blocks-sig)]
                   (reset! index-atom (blocks->children-index new))))

                render-order (atom [])

                ;; Recursive render - each level awaits children
                render-node
                (fn render-node* [node-id]
                  (spin
                   (let [index (await index-maintainer)
                         children-ids (get index node-id [])
                         blocks (:new (track blocks-sig))
                         block (get blocks node-id)]
                     (swap! render-order conj node-id)
                      ;; Recursively render children via parallel
                     {:id node-id
                      :content (:block/content block)
                      :children (vec (when (seq children-ids)
                                       (await (apply parallel
                                                     (map render-node* children-ids)))))})))

                ;; Render from root
                tree-render (render-node :root)
                result (observed-value tree-render)]

            ;; Check structure
            (is (= :root (:id result)))
            (is (= 2 (count (:children result))) "Root has 2 children")
            (is (= :a (:id (first (:children result)))))
            (is (= :b (:id (second (:children result)))))
            (is (= 1 (count (:children (first (:children result)))))
                "A has 1 child")
            (is (= :a1 (:id (first (:children (first (:children result)))))))

            ;; Verify render order includes all nodes
            (is (= #{:root :a :a1 :b} (set @render-order)))))
        (finally
          (v2/release-world! ctx))))))

(deftest test-delta-based-index-maintenance
  (testing "Index can be updated incrementally from deltas"
    (let [ctx (vworld)]
      (try
        (binding [v2/*world* ctx]
          (let [;; Initial blocks
                blocks-sig (v2/signal
                            {:b1 (make-block :b1 nil 0 "B1")
                             :b2 (make-block :b2 :b1 0 "B2")})

                ;; Index with incremental update capability
                index-atom (atom {})
                update-count (atom 0)

                ;; Index maintainer (currently full recompute, could use deltas in future)
                index-maintainer
                (spin
                 (let [{:keys [new]} (track blocks-sig)]
                   (swap! update-count inc)
                   (let [new-index (blocks->children-index new)]
                     (reset! index-atom new-index)
                     new-index)))]

            ;; Initial
            (observed-value index-maintainer)
            (is (= {nil [:b1] :b1 [:b2]} @index-atom))
            (is (= 1 @update-count))

            ;; Add a new block
            (swap! blocks-sig assoc :b3 (make-block :b3 :b1 1 "B3"))

            (is (= {nil [:b1] :b1 [:b2 :b3]} @index-atom))
            (is (= 2 @update-count))))
        (finally
          (v2/release-world! ctx))))))

(deftest test-focus-signal-per-block
  (testing "Focus signal tracked per-block without full tree re-render"
    (let [ctx (vworld)]
      (try
        (binding [v2/*world* ctx]
          (let [focus-sig (v2/signal :b1)  ; Currently focused block

                ;; Per-block signals
                b1-sig (v2/signal (make-block :b1 nil 0 "B1"))
                b2-sig (v2/signal (make-block :b2 nil 1 "B2"))

                b1-render-count (atom 0)
                b2-render-count (atom 0)

                ;; Each block tracks both its data AND focus state
                b1-render
                (spin
                 (let [block-data (track b1-sig)
                       focus-data (track focus-sig)]
                   (swap! b1-render-count inc)
                   {:focused? (= (:new focus-data) :b1)
                    :content (:block/content (:new block-data))}))

                b2-render
                (spin
                 (let [{:keys [new]} (track b2-sig)
                       focus (:new (track focus-sig))]
                   (swap! b2-render-count inc)
                   {:focused? (= focus :b2)
                    :content (:block/content new)}))]

            ;; Initial render
            (observed-value b1-render)
            (observed-value b2-render)
            (is (= 1 @b1-render-count))
            (is (= 1 @b2-render-count))

            ;; Change focus from b1 to b2
            (reset! focus-sig :b2)

;; Both blocks track focus, so both re-render
            ;; This is expected - focus affects multiple blocks
            (is (= 2 @b1-render-count) "B1 re-rendered (was focused)")
            (is (= 2 @b2-render-count) "B2 re-rendered (now focused)")))
        (finally
          (v2/release-world! ctx))))))

(deftest test-collapse-state
  (testing "Collapse state can be stored per-block and affects children visibility"
    (let [ctx (vworld)]
      (try
        (binding [v2/*world* ctx]
          (let [;; Blocks with collapse state in metadata
                blocks-sig (v2/signal
                            {:parent {:block/id :parent
                                      :block/parent nil
                                      :block/order 0
                                      :block/content "Parent"
                                      :block/collapsed? false}
                             :child {:block/id :child
                                     :block/parent :parent
                                     :block/order 0
                                     :block/content "Child"}})

                child-render-count (atom 0)

                ;; Child visibility depends on parent collapse state
                child-render
                (spin
                 (let [{:keys [new]} (track blocks-sig)
                       parent (get new :parent)
                       collapsed? (:block/collapsed? parent)]
                   (swap! child-render-count inc)
                   (when-not collapsed?
                     {:id :child
                      :content (:block/content (get new :child))})))]

            ;; Initial - expanded
            (let [child-result (observed-value child-render)]
              (is (some? child-result) "Child visible when parent expanded"))
            (is (= 1 @child-render-count))

            ;; Collapse parent
            (swap! blocks-sig update :parent assoc :block/collapsed? true)

            (let [child-result (observed-value child-render)]
              (is (nil? child-result) "Child hidden when parent collapsed"))
            (is (= 2 @child-render-count))))
        (finally
          (v2/release-world! ctx))))))
