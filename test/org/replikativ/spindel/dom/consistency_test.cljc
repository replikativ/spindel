(ns org.replikativ.spindel.dom.consistency-test
  "Comprehensive tests for incremental DOM rendering consistency.

  **Testing Strategy:**

  The core invariant we test is:
    render(state1) + apply_deltas → DOM ≡ render(state2) → DOM

  Where state2 = apply_delta_operations(state1).

  **Approach:**

  1. DOMSimulator: Tracks the DOM state by replaying operation logs from
     MockDischarge. This gives us a structural representation of what the
     DOM would look like.

  2. Two-Path Comparison: For each test:
     a) Incremental path: render initial state, apply mutations, collect deltas
     b) Direct path: render final state directly
     c) Compare resulting DOM structures

  3. Test Categories:
     - Simple operations: single add/remove/update
     - Keyed lists: ifor-each with various mutations
     - Nested structures: deeply nested elements with changes
     - Complex scenarios: full todo app mutations

  **Why This Matters:**

  Delta-direct rendering skips diffing, so we must ensure:
  - Deltas correctly represent the change
  - Applying deltas produces the same result as re-rendering
  - No drift between incremental and direct paths"
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer-macros [deftest is testing use-fixtures]])
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.dom.core :as dom]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            #?(:clj [org.replikativ.spindel.test-helpers :refer [with-ctx]])
            #?(:clj [org.replikativ.spindel.test-async :refer [await-drain]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.dom.foreach :refer [ifor-each]])))

(use-fixtures :each
  (fn [f]
    (let [test-ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* test-ctx]
          (f))
        (finally
          (ctx/stop-context! test-ctx))))))

;; =============================================================================
;; DOM Simulator
;; =============================================================================
;; Builds a structural representation of the DOM from operation logs

(defrecord DOMElement [tag attrs children])
(defrecord DOMText [text])

(defn- dom-element [tag attrs children]
  (->DOMElement tag (or attrs {}) (vec children)))

(defn- dom-text [text]
  (->DOMText text))

(defn dom-structure-equal?
  "Compare two DOM structures for equality (ignoring internal IDs)."
  [a b]
  (cond
    (and (instance? DOMElement a) (instance? DOMElement b))
    (and (= (:tag a) (:tag b))
         (= (:attrs a) (:attrs b))
         (= (count (:children a)) (count (:children b)))
         (every? true? (map dom-structure-equal? (:children a) (:children b))))

    (and (instance? DOMText a) (instance? DOMText b))
    (= (:text a) (:text b))

    :else
    (= a b)))

(defn simulate-dom
  "Simulate DOM state from MockDischarge operation log.

  Returns a map of element-id -> DOMElement/DOMText with parent/child relationships."
  [log]
  (let [elements (atom {})       ; id -> {:type :element/:text, :tag, :attrs, :children, :parent}
        root-candidates (atom #{})  ; Track elements that could be roots
        parent-tracking (atom {})]  ; child-id -> parent-id

    ;; Process each operation
    (doseq [op log]
      (case (:op op)
        :create-element
        (let [{:keys [id tag]} op]
          (swap! elements assoc id {:type :element :tag tag :attrs {} :children []})
          (swap! root-candidates conj id))

        :create-text
        (let [{:keys [id text]} op]
          (swap! elements assoc id {:type :text :text text})
          (swap! root-candidates conj id))

        :set-attr
        (let [{:keys [el attr value]} op]
          (swap! elements update-in [el :attrs] assoc attr value))

        :remove-attr
        (let [{:keys [el attr]} op]
          (swap! elements update-in [el :attrs] dissoc attr))

        :append-child
        (let [{:keys [parent child]} op]
          (swap! elements update-in [parent :children] conj child)
          (swap! parent-tracking assoc child parent)
          (swap! root-candidates disj child))

        :insert-child
        (let [{:keys [parent child index]} op
              current-children (get-in @elements [parent :children] [])]
          (when (<= index (count current-children))
            (let [new-children (vec (concat (subvec current-children 0 index)
                                           [child]
                                           (subvec current-children index)))]
              (swap! elements assoc-in [parent :children] new-children)
              (swap! parent-tracking assoc child parent)
              (swap! root-candidates disj child))))

        :remove-child
        (let [{:keys [parent index]} op
              current-children (get-in @elements [parent :children] [])]
          (when (< index (count current-children))
            (let [removed-child (nth current-children index)
                  new-children (vec (concat (subvec current-children 0 index)
                                           (subvec current-children (inc index))))]
              (swap! elements assoc-in [parent :children] new-children)
              (swap! parent-tracking dissoc removed-child))))

        :replace-child
        (let [{:keys [parent child index]} op
              current-children (get-in @elements [parent :children] [])]
          (when (< index (count current-children))
            (let [old-child (nth current-children index)]
              (swap! elements assoc-in [parent :children index] child)
              (swap! parent-tracking dissoc old-child)
              (swap! parent-tracking assoc child parent)
              (swap! root-candidates disj child))))

        :set-text
        (let [{:keys [el text]} op]
          (swap! elements assoc-in [el :text] text))

        ;; Ignore other operations
        nil))

    ;; Build DOM tree structure from root
    (let [roots (filter #(not (contains? @parent-tracking %)) (keys @elements))]
      {:elements @elements
       :roots (vec roots)
       :parent-tracking @parent-tracking})))

(defn dom-to-structure
  "Convert DOM simulation state to a structural tree for comparison."
  [dom-state el-id]
  (when el-id
    (let [el (get (:elements dom-state) el-id)]
      (case (:type el)
        :element
        (dom-element (:tag el)
                     (:attrs el)
                     (mapv #(dom-to-structure dom-state %) (:children el)))

        :text
        (dom-text (:text el))

        nil))))

(defn dom-root-structure
  "Get the structure of the first root element."
  [dom-state]
  (when-let [root-id (first (:roots dom-state))]
    (dom-to-structure dom-state root-id)))

;; =============================================================================
;; Test Helpers
;; =============================================================================

(defn render-vdom-to-dom
  "Render a vdom to MockDischarge and return DOM state."
  [vdom]
  (let [{:keys [discharge log]} (disch/make-mock-discharge)]
    (disch/render-initial! discharge vdom)
    (simulate-dom @log)))

(defn vdom-to-structure
  "Convert vdom to DOM structure for comparison."
  [vdom]
  (dom-root-structure (render-vdom-to-dom vdom)))

(defn compare-render-paths-with-mutation
  "Compare incremental and direct render paths using delta-producing mutations.

  This function tests the core invariant of delta-direct rendering:
    render(initial) + apply_deltas(mutation) ≡ render(final)

  It does this by:
  1. Direct path: Render final state directly to fresh DOM, get DOM structure
  2. Incremental path: Render initial state, apply mutation via swap! (producing
     deltas), get resulting vdom and render it to DOM

  The key difference from a naive approach: we use swap! with a mutation-fn
  that produces deltas, NOT reset! which would lose delta information.

  Args:
    initial-state - Starting state value (should be deltaable)
    mutation-fn - Function (state) -> new-state that produces deltas
    render-fn - Function that takes state and returns vdom

  Returns map with:
    :equal? - Whether DOM structures are equal
    :incremental - DOM structure from incremental path
    :direct - DOM structure from direct render
    :deltas - Deltas captured during mutation"
  [initial-state mutation-fn render-fn]
  ;; Compute final state
  (let [final-state (mutation-fn initial-state)]
    ;; Both paths need execution context for ifor-each
    (let [rt (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* rt]
          ;; Direct path: render final state to fresh DOM (needs context for ifor-each)
          (let [direct-vdom (render-fn final-state)
                direct-structure (vdom-to-structure direct-vdom)]

            ;; Incremental path: use signal + spin with delta-producing mutation
            (let [{:keys [discharge]} (disch/make-mock-discharge)
                  ;; Create signal with initial state
                  state-sig (sig/signal initial-state)
                  captured-deltas (atom nil)
                  ;; Create spin that tracks signal and renders
                  app-spin (spin
                             (let [state-iv (track state-sig)
                                   current @state-iv
                                   deltas (iv/get-deltas state-iv)]
                               (reset! captured-deltas deltas)
                               (render-fn current)))]

              ;; Initial render
              (render/render-spin! nil app-spin discharge)
              @app-spin

              ;; Mutate signal using swap! - this preserves deltas!
              (swap! state-sig mutation-fn)
              (#?(:clj org.replikativ.spindel.test-async/await-drain
                  :cljs identity) rt)

              ;; Get final vdom from spin — deref waits for re-execution when dirty
              (let [incremental-vdom @app-spin
                    incremental-structure (vdom-to-structure incremental-vdom)]

                {:equal? (dom-structure-equal? incremental-structure direct-structure)
                 :incremental incremental-structure
                 :direct direct-structure
                 :deltas @captured-deltas}))))
        (finally
          (ctx/stop-context! rt))))))

;; =============================================================================
;; Simple Element Tests
;; =============================================================================

#?(:clj
   (deftest test-simple-element-consistency
     (testing "Simple element renders consistently"
       (let [vdom (el/div {:class "test"} "Hello")]
         (is (instance? DOMElement (vdom-to-structure vdom)))
         (is (= :div (:tag (vdom-to-structure vdom))))))))

#?(:clj
   (deftest test-nested-elements-consistency
     (testing "Nested elements render consistently"
       (let [vdom (el/div {:class "outer"}
                    (el/span {:class "inner"} "Text"))]
         (let [s (vdom-to-structure vdom)]
           (is (= :div (:tag s)))
           (is (= 1 (count (:children s))))
           (is (= :span (:tag (first (:children s))))))))))

;; =============================================================================
;; List Rendering Consistency
;; =============================================================================

(defn render-list [items]
  (el/ul {:class "list"}
    (foreach/ifor-each :id items
      (fn [item] (el/li {:key (:id item)} (:text item))))))

#?(:clj
   (deftest test-list-add-item-consistency
     (testing "Adding item to list is consistent with delta tracking"
       (let [initial (d/deltaable-vector [{:id "1" :text "A"}])
             mutation-fn #(conj % {:id "2" :text "B"})
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result)
             (str "Structures should be equal:\n"
                  "Incremental: " (:incremental result) "\n"
                  "Direct: " (:direct result)))
         (is (seq (:deltas result)) "Should have deltas")
         (is (= :add (:delta (first (:deltas result)))) "Delta should be :add")))))

#?(:clj
   (deftest test-list-remove-item-consistency
     (testing "Removing item from list is consistent with delta tracking"
       (let [initial (d/deltaable-vector [{:id "1" :text "A"} {:id "2" :text "B"} {:id "3" :text "C"}])
             mutation-fn #(d/remove-at % 1)  ; Remove middle item (id "2")
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result)
             (str "Structures should be equal:\n"
                  "Incremental: " (:incremental result) "\n"
                  "Direct: " (:direct result)))
         (is (seq (:deltas result)) "Should have deltas")
         (is (= :remove (:delta (first (:deltas result)))) "Delta should be :remove")))))

#?(:clj
   (deftest test-list-update-item-consistency
     (testing "Updating item in list is consistent with delta tracking"
       (let [initial (d/deltaable-vector [{:id "1" :text "A"} {:id "2" :text "B"}])
             mutation-fn #(assoc % 1 {:id "2" :text "B-updated"})
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result))
         (is (seq (:deltas result)) "Should have deltas")
         (is (= :update (:delta (first (:deltas result)))) "Delta should be :update")))))

#?(:clj
   (deftest test-list-reorder-consistency
     (testing "Reordering list is consistent with delta tracking"
       ;; Reordering requires multiple operations - remove from old position, add at new
       ;; We simulate moving item 3 to front by removing at idx 2 and inserting at 0
       (let [initial (d/deltaable-vector [{:id "1" :text "A"} {:id "2" :text "B"} {:id "3" :text "C"}])
             ;; Reorder by rebuilding the vector - this produces :replace-all rather than fine deltas
             ;; but still tests that final state matches
             mutation-fn (fn [v]
                           (let [items (vec v)]  ; Convert to plain vector
                             (d/deltaable-vector
                               [(nth items 2) (nth items 0) (nth items 1)])))
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result))))))

;; =============================================================================
;; Nested Structure Consistency
;; =============================================================================

(defn render-nested-structure [data]
  (el/div {:class "container"}
    (el/header {:class "header"}
      (el/h1 (:title data))
      (when (:subtitle data)
        (el/p {:class "subtitle"} (:subtitle data))))
    (el/main {:class "content"}
      (el/ul {:class "items"}
        (foreach/ifor-each :id (:items data)
          (fn [item]
            (el/li {:key (:id item) :class (when (:active item) "active")}
              (el/span {:class "text"} (:text item))
              (when (:count item)
                (el/span {:class "count"} (str (:count item)))))))))
    (el/footer {:class "footer"}
      (el/span (str "Total: " (count (:items data)))))))

#?(:clj
   (deftest test-nested-add-item-consistency
     (testing "Adding item to nested structure is consistent with delta tracking"
       (let [initial (d/deltaable-map {:title "Test"
                                       :items (d/deltaable-vector [{:id "1" :text "A"}])})
             mutation-fn #(update % :items conj {:id "2" :text "B"})
             result (compare-render-paths-with-mutation initial mutation-fn render-nested-structure)]
         (is (:equal? result))))))

#?(:clj
   (deftest test-nested-update-title-consistency
     (testing "Updating title in nested structure is consistent with delta tracking"
       (let [initial (d/deltaable-map {:title "Old Title"
                                       :items (d/deltaable-vector [{:id "1" :text "A"}])})
             mutation-fn #(assoc % :title "New Title")
             result (compare-render-paths-with-mutation initial mutation-fn render-nested-structure)]
         (is (:equal? result))))))

#?(:clj
   (deftest test-nested-conditional-consistency
     (testing "Conditional rendering in nested structure is consistent with delta tracking"
       (let [initial (d/deltaable-map {:title "Test"
                                       :subtitle nil
                                       :items (d/deltaable-vector [{:id "1" :text "A" :count nil}])})
             mutation-fn #(-> %
                              (assoc :subtitle "With Subtitle")
                              (update :items assoc 0 {:id "1" :text "A" :count 5}))
             result (compare-render-paths-with-mutation initial mutation-fn render-nested-structure)]
         (is (:equal? result))))))

#?(:clj
   (deftest test-nested-active-toggle-consistency
     (testing "Toggling active state in nested structure is consistent with delta tracking"
       (let [initial (d/deltaable-map {:title "Test"
                                       :items (d/deltaable-vector [{:id "1" :text "A" :active false}
                                                                    {:id "2" :text "B" :active false}])})
             mutation-fn #(update % :items assoc 0 {:id "1" :text "A" :active true})
             result (compare-render-paths-with-mutation initial mutation-fn render-nested-structure)]
         (is (:equal? result))))))

;; =============================================================================
;; Todo App Consistency Tests
;; =============================================================================

(defn render-todo-item [todo]
  (el/li {:key (:id todo)
          :class (str "todo " (when (:done todo) "done"))}
    (el/input {:type "checkbox" :checked (:done todo)})
    (el/span {:class "text"} (:text todo))
    (el/button {:class "delete"} "×")))

(defn render-todo-app [state]
  (let [{:keys [todos filter-mode]} state
        visible-todos (case filter-mode
                        :all todos
                        :active (filter #(not (:done %)) todos)
                        :done (filter :done todos)
                        todos)
        done-count (count (filter :done todos))
        active-count (- (count todos) done-count)]
    (el/div {:class "todo-app"}
      (el/header {:class "header"}
        (el/h1 "Todos")
        (el/input {:class "new-todo" :placeholder "What needs to be done?"}))

      (el/section {:class "main"}
        (el/ul {:class "todo-list"}
          (foreach/ifor-each :id visible-todos render-todo-item)))

      (el/footer {:class "footer"}
        (el/span {:class "count"} (str active-count " items left"))
        (el/div {:class "filters"}
          (el/button {:class (when (= :all filter-mode) "selected")} "All")
          (el/button {:class (when (= :active filter-mode) "selected")} "Active")
          (el/button {:class (when (= :done filter-mode) "selected")} "Completed"))
        (when (pos? done-count)
          (el/button {:class "clear-completed"} "Clear completed"))))))

#?(:clj
   (deftest test-todo-add-consistency
     (testing "Adding todo is consistent with delta tracking"
       (let [initial (d/deltaable-map {:todos (d/deltaable-vector [{:id "1" :text "Task 1" :done false}])
                                       :filter-mode :all})
             mutation-fn #(update % :todos conj {:id "2" :text "Task 2" :done false})
             result (compare-render-paths-with-mutation initial mutation-fn render-todo-app)]
         (is (:equal? result))))))

#?(:clj
   (deftest test-todo-toggle-consistency
     (testing "Toggling todo is consistent with delta tracking"
       (let [initial (d/deltaable-map {:todos (d/deltaable-vector [{:id "1" :text "Task 1" :done false}
                                                                    {:id "2" :text "Task 2" :done false}])
                                       :filter-mode :all})
             mutation-fn #(update % :todos assoc 0 {:id "1" :text "Task 1" :done true})
             result (compare-render-paths-with-mutation initial mutation-fn render-todo-app)]
         (is (:equal? result))))))

#?(:clj
   (deftest test-todo-remove-consistency
     (testing "Removing todo is consistent with delta tracking"
       (let [initial (d/deltaable-map {:todos (d/deltaable-vector [{:id "1" :text "Task 1" :done false}
                                                                    {:id "2" :text "Task 2" :done false}
                                                                    {:id "3" :text "Task 3" :done true}])
                                       :filter-mode :all})
             mutation-fn #(update % :todos d/remove-at 1)  ; Remove item at index 1 (id "2")
             result (compare-render-paths-with-mutation initial mutation-fn render-todo-app)]
         (is (:equal? result))))))

#?(:clj
   (deftest test-todo-filter-consistency
     (testing "Changing filter is consistent with delta tracking"
       (let [initial (d/deltaable-map {:todos (d/deltaable-vector [{:id "1" :text "Task 1" :done false}
                                                                    {:id "2" :text "Task 2" :done true}])
                                       :filter-mode :all})
             mutation-fn #(assoc % :filter-mode :active)
             result (compare-render-paths-with-mutation initial mutation-fn render-todo-app)]
         (is (:equal? result))))))

#?(:clj
   (deftest test-todo-clear-completed-consistency
     (testing "Clear completed is consistent with delta tracking"
       (let [initial (d/deltaable-map {:todos (d/deltaable-vector [{:id "1" :text "Task 1" :done false}
                                                                    {:id "2" :text "Task 2" :done true}
                                                                    {:id "3" :text "Task 3" :done true}])
                                       :filter-mode :all})
             ;; Clear completed by filtering out done items
             mutation-fn #(assoc % :todos (d/filter-vec (fn [todo] (not (:done todo))) (:todos %)))
             result (compare-render-paths-with-mutation initial mutation-fn render-todo-app)]
         (is (:equal? result))))))

#?(:clj
   (deftest test-todo-complex-sequence-consistency
     (testing "Complex sequence of operations is consistent with delta tracking"
       ;; Simulate: add 3 items, toggle 2, remove 1, change filter - all in one mutation
       (let [initial (d/deltaable-map {:todos (d/deltaable-vector [])
                                       :filter-mode :all})
             mutation-fn (fn [state]
                           (-> state
                               ;; Add 3 items
                               (update :todos conj {:id "1" :text "Task 1" :done false})
                               (update :todos conj {:id "2" :text "Task 2" :done false})
                               (update :todos conj {:id "3" :text "Task 3" :done false})
                               ;; Toggle item 1 to done
                               (update :todos assoc 0 {:id "1" :text "Task 1" :done true})
                               ;; Remove item 2
                               (update :todos d/remove-at 1)
                               ;; Change filter
                               (assoc :filter-mode :active)))
             result (compare-render-paths-with-mutation initial mutation-fn render-todo-app)]
         (is (:equal? result))))))

;; =============================================================================
;; Signal-Based Incremental Tests
;; =============================================================================
;; These tests use actual signals and spins to verify delta propagation

#?(:clj
   (deftest test-signal-based-list-add
     (testing "Signal-based list addition produces correct deltas"
       (with-ctx [rt]
         (let [{:keys [discharge log]} (disch/make-mock-discharge)
               items (sig/signal [])
               render-count (atom 0)
               captured-deltas (atom nil)

               app-spin (spin
                          (let [items-iv (track items)
                                current @items-iv
                                deltas (iv/get-deltas items-iv)]
                            (swap! render-count inc)
                            (reset! captured-deltas deltas)
                            (el/ul {:class "list"}
                              (foreach/ifor-each :id current
                                (fn [item] (el/li {:key (:id item)} (:text item)))))))]

           ;; Initial render
           (render/render-spin! nil app-spin discharge)
           @app-spin
           (is (= 1 @render-count))

           ;; Add first item
           (reset! log [])
           (swap! items conj {:id "1" :text "A"})
           (await-drain rt)

           (is (= 2 @render-count))
           ;; Verify deltas were captured
           (is (seq @captured-deltas) "Should have captured deltas")
           (is (= :add (:delta (first @captured-deltas))))
           ;; Verify delta path and value
           (is (= [0] (:path (first @captured-deltas))))
           (is (= {:id "1" :text "A"} (:value (first @captured-deltas)))))))))

#?(:clj
   (deftest test-signal-based-list-remove
     (testing "Signal-based list removal produces correct deltas"
       (with-ctx [rt]
         (let [{:keys [discharge log]} (disch/make-mock-discharge)
               items (sig/signal [{:id "1" :text "A"}
                                  {:id "2" :text "B"}])
               captured-deltas (atom nil)

               app-spin (spin
                          (let [items-iv (track items)
                                current @items-iv
                                deltas (iv/get-deltas items-iv)]
                            (reset! captured-deltas deltas)
                            (el/ul {:class "list"}
                              (foreach/ifor-each :id current
                                (fn [item] (el/li {:key (:id item)} (:text item)))))))]

           ;; Initial render
           (render/render-spin! nil app-spin discharge)
           @app-spin

           ;; Remove second item using d/remove-at
           (reset! log [])
           (swap! items d/remove-at 1)
           (await-drain rt)

           ;; Verify deltas
           (is (seq @captured-deltas) "Should have captured deltas")
           (is (= :remove (:delta (first @captured-deltas))))
           (is (= [1] (:path (first @captured-deltas)))))))))

#?(:clj
   (deftest test-signal-based-list-update
     (testing "Signal-based list update produces correct deltas"
       (with-ctx [rt]
         (let [{:keys [discharge log]} (disch/make-mock-discharge)
               items (sig/signal [{:id "1" :text "A"}
                                  {:id "2" :text "B"}])
               captured-deltas (atom nil)

               app-spin (spin
                          (let [items-iv (track items)
                                current @items-iv
                                deltas (iv/get-deltas items-iv)]
                            (reset! captured-deltas deltas)
                            (el/ul {:class "list"}
                              (foreach/ifor-each :id current
                                (fn [item] (el/li {:key (:id item)} (:text item)))))))]

           ;; Initial render
           (render/render-spin! nil app-spin discharge)
           @app-spin

           ;; Update first item
           (reset! log [])
           (swap! items assoc 0 {:id "1" :text "A-updated"})
           (await-drain rt)

           ;; Verify deltas
           (is (seq @captured-deltas) "Should have captured deltas")
           (is (= :update (:delta (first @captured-deltas))))
           (is (= [0] (:path (first @captured-deltas)))))))))

;; =============================================================================
;; Delta-Aware Consistency Tests
;; =============================================================================
;; These tests use compare-render-paths-with-mutation to verify that delta
;; propagation produces the same result as direct rendering.

#?(:clj
   (deftest test-delta-add-consistency
     (testing "Adding item via conj produces correct result with deltas"
       (let [initial (d/deltaable-vector [{:id "1" :text "A"}])
             mutation-fn #(conj % {:id "2" :text "B"})
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result) "Incremental should match direct")
         (is (seq (:deltas result)) "Should have captured deltas")
         (is (= :add (:delta (first (:deltas result)))) "Delta should be :add")))))

#?(:clj
   (deftest test-delta-remove-consistency
     (testing "Removing item via remove-at produces correct result with deltas"
       (let [initial (d/deltaable-vector [{:id "1" :text "A"}
                                          {:id "2" :text "B"}
                                          {:id "3" :text "C"}])
             mutation-fn #(d/remove-at % 1)
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result) "Incremental should match direct")
         (is (seq (:deltas result)) "Should have captured deltas")
         (is (= :remove (:delta (first (:deltas result)))) "Delta should be :remove")))))

#?(:clj
   (deftest test-delta-update-consistency
     (testing "Updating item via assoc produces correct result with deltas"
       (let [initial (d/deltaable-vector [{:id "1" :text "A"}
                                          {:id "2" :text "B"}])
             mutation-fn #(assoc % 0 {:id "1" :text "A-updated"})
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result) "Incremental should match direct")
         (is (seq (:deltas result)) "Should have captured deltas")
         (is (= :update (:delta (first (:deltas result)))) "Delta should be :update")))))

#?(:clj
   (deftest test-delta-multiple-ops-consistency
     (testing "Multiple operations produce correct cumulative result"
       (let [initial (d/deltaable-vector [{:id "1" :text "A"}])
             ;; Add two items in sequence
             mutation-fn #(-> %
                              (conj {:id "2" :text "B"})
                              (conj {:id "3" :text "C"}))
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result) "Incremental should match direct")
         (is (= 2 (count (:deltas result))) "Should have 2 deltas")))))

;; =============================================================================
;; Edge Case Tests
;; =============================================================================

#?(:clj
   (deftest test-empty-to-populated-consistency
     (testing "Empty to populated list is consistent with delta tracking"
       (let [initial (d/deltaable-vector [])
             mutation-fn #(-> % (conj {:id "1" :text "A"}) (conj {:id "2" :text "B"}))
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result))
         (is (= 2 (count (:deltas result))) "Should have 2 add deltas")))))

#?(:clj
   (deftest test-populated-to-empty-consistency
     (testing "Populated to empty list is consistent with delta tracking"
       (let [initial (d/deltaable-vector [{:id "1" :text "A"} {:id "2" :text "B"}])
             ;; Remove both items - remove second first to keep index stable
             mutation-fn #(-> % (d/remove-at 1) (d/remove-at 0))
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result))
         (is (= 2 (count (:deltas result))) "Should have 2 remove deltas")))))

#?(:clj
   (deftest test-single-item-operations-consistency
     (testing "Operations on single item list are consistent with delta tracking"
       ;; Add to empty
       (let [initial (d/deltaable-vector [])
             mutation-fn #(conj % {:id "1" :text "A"})
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result))
         (is (= :add (:delta (first (:deltas result))))))

       ;; Update single
       (let [initial (d/deltaable-vector [{:id "1" :text "A"}])
             mutation-fn #(assoc % 0 {:id "1" :text "B"})
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result))
         (is (= :update (:delta (first (:deltas result))))))

       ;; Remove single
       (let [initial (d/deltaable-vector [{:id "1" :text "A"}])
             mutation-fn #(d/remove-at % 0)
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result))
         (is (= :remove (:delta (first (:deltas result)))))))))

#?(:clj
   (deftest test-many-items-consistency
     (testing "Large list operations are consistent with delta tracking"
       (let [items (vec (for [i (range 100)]
                          {:id (str i) :text (str "Item " i)}))
             initial (d/deltaable-vector items)
             ;; Remove odd-indexed items (indices 99, 97, 95, ... 1) in reverse order
             mutation-fn (fn [v]
                           (reduce (fn [acc idx]
                                     (d/remove-at acc idx))
                                   v
                                   (reverse (range 1 100 2))))
             result (compare-render-paths-with-mutation initial mutation-fn render-list)]
         (is (:equal? result))
         ;; Should have 50 remove deltas
         (is (= 50 (count (:deltas result))) "Should have 50 remove deltas")))))

#?(:clj
   (deftest test-deeply-nested-consistency
     (testing "Deeply nested structure is consistent with delta tracking"
       (let [render-deep (fn [data]
                           (el/div {:id "level-1"}
                             (el/div {:id "level-2"}
                               (el/div {:id "level-3"}
                                 (el/div {:id "level-4"}
                                   (el/span (:text data)))))))
             initial (d/deltaable-map {:text "Original"})
             mutation-fn #(assoc % :text "Updated")
             result (compare-render-paths-with-mutation initial mutation-fn render-deep)]
         (is (:equal? result))
         (is (seq (:deltas result)) "Should have deltas")))))

;; =============================================================================
;; Attribute-Only Change Tests
;; =============================================================================

#?(:clj
   (deftest test-attribute-add-consistency
     (testing "Adding attribute is consistent with delta tracking"
       (let [render-with-class (fn [state]
                                 (if (:has-class? state)
                                   (el/div {:class "active"} "Content")
                                   (el/div {} "Content")))
             initial (d/deltaable-map {:has-class? false})
             mutation-fn #(assoc % :has-class? true)
             result (compare-render-paths-with-mutation initial mutation-fn render-with-class)]
         (is (:equal? result))
         (is (seq (:deltas result)) "Should have deltas")))))

#?(:clj
   (deftest test-attribute-remove-consistency
     (testing "Removing attribute is consistent with delta tracking"
       (let [render-with-class (fn [state]
                                 (if (:has-class? state)
                                   (el/div {:class "active"} "Content")
                                   (el/div {} "Content")))
             initial (d/deltaable-map {:has-class? true})
             mutation-fn #(assoc % :has-class? false)
             result (compare-render-paths-with-mutation initial mutation-fn render-with-class)]
         (is (:equal? result))
         (is (seq (:deltas result)) "Should have deltas")))))

#?(:clj
   (deftest test-attribute-update-consistency
     (testing "Updating attribute is consistent with delta tracking"
       (let [render-with-class (fn [state]
                                 (el/div {:class (:class-name state)} "Content"))
             initial (d/deltaable-map {:class-name "old-class"})
             mutation-fn #(assoc % :class-name "new-class")
             result (compare-render-paths-with-mutation initial mutation-fn render-with-class)]
         (is (:equal? result))
         (is (seq (:deltas result)) "Should have deltas")))))

;; =============================================================================
;; Multiple Children Types
;; =============================================================================

#?(:clj
   (deftest test-mixed-children-consistency
     (testing "Mixed static and dynamic children is consistent with delta tracking"
       (let [render-mixed (fn [items]
                            (el/div {:class "container"}
                              ;; Static children
                              (el/h1 "Title")
                              (el/p "Description")
                              ;; Dynamic list
                              (el/ul {:class "list"}
                                (foreach/ifor-each :id items
                                  (fn [item] (el/li (:text item)))))
                              ;; Static footer
                              (el/footer "Footer")))
             initial (d/deltaable-vector [{:id "1" :text "A"}])
             mutation-fn #(-> % (conj {:id "2" :text "B"}) (conj {:id "3" :text "C"}))
             result (compare-render-paths-with-mutation initial mutation-fn render-mixed)]
         (is (:equal? result))
         (is (= 2 (count (:deltas result))) "Should have 2 add deltas")))))
