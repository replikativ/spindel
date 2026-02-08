(ns org.replikativ.spindel.dom.todo-app-test
  "Integration test demonstrating a complete todo app with reactive DOM rendering.

  This test shows the full reactive cycle:
  1. Signal with deltaable collection
  2. Spin that tracks signal and produces vdom
  3. Render effect that mounts and updates DOM
  4. Signal mutations trigger re-renders

  **Delta-Direct Rendering (New Model):**
  - Element macros capture source location for stable addressing
  - Slot-based caching produces deltas without diffing
  - ifor-each macro returns KeyedFragment with deltas
  - Tests verify O(delta) behavior by counting render calls"
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.state.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            #?(:clj [org.replikativ.spindel.test-async :refer [await-drain]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.dom.foreach :refer [ifor-each]])))

;; =============================================================================
;; Todo Item Rendering
;; =============================================================================

(defn render-todo-item
  "Render a single todo item to vdom."
  [todo]
  (el/li {:key (:id todo)
          :class (if (:done todo) "done" "pending")}
    (el/span {:class "todo-text"} (:text todo))
    (el/button {:class "toggle"} (if (:done todo) "Undo" "Done"))
    (el/button {:class "delete"} "Delete")))

#?(:clj
   (defn render-todo-list
     "Render the full todo list vdom.

     Uses ifor-each with proper execution context."
     [todos-value]
     ;; Deltaables implement Seqable, Counted, etc. - use directly without deref
     (el/div {:class "todo-app"}
       (el/h1 "Todo List")
       (el/div {:class "stats"}
         (el/span (str "Total: " (count todos-value)))
         (el/span (str " | Done: " (count (filter :done todos-value)))))
       (el/ul {:class "todo-list"}
         (foreach/ifor-each :id todos-value render-todo-item)))))

;; =============================================================================
;; Basic Integration Tests
;; =============================================================================

#?(:clj
   (deftest test-todo-app-initial-render
     (testing "Todo app renders initial empty state"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge log]} (disch/make-mock-discharge)
                 todos (sig/signal [])
                 app-spin (spin
                            (let [{:keys [new]} (track todos)]
                              ;; Just pass deltaable directly - stays in deltaable domain
                              (render-todo-list new)))
                 container nil]

             ;; Initial render
             (render/render-spin! container app-spin discharge)
             @app-spin

             ;; Verify structure created
             (is (some #(= :create-element (:op %)) @log)
                 "Should create elements")
             (is (some #(and (= :create-element (:op %))
                             (= :div (:tag %))) @log)
                 "Should create div container")
             (is (some #(and (= :create-element (:op %))
                             (= :h1 (:tag %))) @log)
                 "Should create h1 header")
             (is (some #(and (= :create-element (:op %))
                             (= :ul (:tag %))) @log)
                 "Should create ul list")))))))

#?(:clj
   (deftest test-todo-app-add-item
     (testing "Adding todo item triggers re-render"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge log]} (disch/make-mock-discharge)
                 todos (sig/signal [])
                 render-count (atom 0)
                 app-spin (spin
                            (let [{:keys [new]} (track todos)]
                              (swap! render-count inc)
                              (render-todo-list new)))
                 container nil]

             ;; Initial render
             (render/render-spin! container app-spin discharge)
             @app-spin
             (is (= 1 @render-count))

             ;; Clear log
             (reset! log [])

             ;; Add a todo
             (swap! todos conj {:id "1" :text "Buy milk" :done false})
             (await-drain rt)

             ;; Verify re-render happened
             (is (= 2 @render-count) "Should re-render after adding todo")))))))

#?(:clj
   (deftest test-todo-app-multiple-items
     (testing "Multiple todos render correctly"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge]} (disch/make-mock-discharge)
                 todos (sig/signal [])
                 last-item-count (atom 0)
                 app-spin (spin
                            (let [{:keys [new]} (track todos)]
                              ;; Deltaables implement Counted - use directly
                              (reset! last-item-count (count new))
                              (render-todo-list new)))
                 container nil]

             ;; Initial render
             (render/render-spin! container app-spin discharge)
             @app-spin
             (is (= 0 @last-item-count))

             ;; Add first todo
             (swap! todos conj {:id "1" :text "Buy milk" :done false})
             (await-drain rt)
             @app-spin
             (is (= 1 @last-item-count))

             ;; Add second todo
             (swap! todos conj {:id "2" :text "Walk dog" :done false})
             (await-drain rt)
             @app-spin
             (is (= 2 @last-item-count))

             ;; Add third todo
             (swap! todos conj {:id "3" :text "Write code" :done true})
             (await-drain rt)
             @app-spin
             (is (= 3 @last-item-count))))))))

#?(:clj
   (deftest test-todo-app-update-item
     (testing "Updating todo triggers re-render with new state"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge]} (disch/make-mock-discharge)
                 todos (sig/signal [{:id "1" :text "Buy milk" :done false}])
                 last-done-status (atom nil)
                 app-spin (spin
                            (let [{:keys [new]} (track todos)]
                              ;; Deltaables implement Seqable - first works directly
                              (reset! last-done-status (:done (first new)))
                              (render-todo-list new)))
                 container nil]

             ;; Initial render
             (render/render-spin! container app-spin discharge)
             @app-spin
             (is (= false @last-done-status))

             ;; Toggle done status - use assoc on deltaable vector directly
             ;; This produces proper :update deltas
             (swap! todos
                    (fn [v]
                      ;; Find the index and update in place
                      (let [idx (first (keep-indexed #(when (= (:id %2) "1") %1) v))]
                        (when idx
                          (assoc v idx (update (nth v idx) :done not))))))
             (await-drain rt)

             ;; Verify re-render with new status
             (is (= true @last-done-status) "Should show done status after toggle")))))))

#?(:clj
   (deftest test-todo-app-stats-update
     (testing "Stats update correctly when items change"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge]} (disch/make-mock-discharge)
                 todos (sig/signal [])
                 last-stats (atom {:total 0 :done 0})
                 app-spin (spin
                            (let [{:keys [new]} (track todos)]
                              ;; Deltaables implement Seqable/Counted - use directly
                              (reset! last-stats
                                      {:total (count new)
                                       :done (count (filter :done new))})
                              (render-todo-list new)))
                 container nil]

             ;; Initial render
             (render/render-spin! container app-spin discharge)
             @app-spin
             (is (= {:total 0 :done 0} @last-stats))

             ;; Add pending todo
             (swap! todos conj {:id "1" :text "Task 1" :done false})
             (await-drain rt)
             (is (= {:total 1 :done 0} @last-stats))

             ;; Add done todo
             (swap! todos conj {:id "2" :text "Task 2" :done true})
             (await-drain rt)
             (is (= {:total 2 :done 1} @last-stats))

             ;; Add another pending
             (swap! todos conj {:id "3" :text "Task 3" :done false})
             (await-drain rt)
             (is (= {:total 3 :done 1} @last-stats))))))))

;; =============================================================================
;; KeyedFragment Tests
;; =============================================================================

#?(:clj
   (deftest test-ifor-each-returns-keyed-fragment
     (testing "ifor-each returns KeyedFragment"
       (let [ctx (ctx/create-execution-context)]
         (binding [rtc/*execution-context* ctx]
           (let [items [{:id "1" :text "A"} {:id "2" :text "B"}]
                 render-fn (fn [item] (el/li (:text item)))
                 result (foreach/ifor-each :id items render-fn)]
             (is (frag/keyed-fragment? result) "Should return KeyedFragment")
             (is (= 2 (count (frag/fragment-items result))) "Should have 2 items")))))))

#?(:clj
   (deftest test-keyed-fragment-in-parent
     (testing "KeyedFragment renders correctly as child of element"
       (let [{:keys [discharge log]} (disch/make-mock-discharge)
             items [(el/li "A") (el/li "B") (el/li "C")]
             fragment (frag/keyed-fragment items nil)
             parent (el/ul fragment)]
         ;; Render the parent
         (disch/render-initial! discharge parent)
         (let [ops @log]
           ;; Should create ul + 3 li + 3 text
           (is (= 1 (count (filter #(and (= :create-element (:op %))
                                         (= :ul (:tag %))) ops)))
               "Should create ul")
           (is (= 3 (count (filter #(and (= :create-element (:op %))
                                         (= :li (:tag %))) ops)))
               "Should create 3 li elements"))))))

;; =============================================================================
;; Element Macro Tests in Simple Mode
;; =============================================================================

#?(:clj
   (deftest test-element-macros-no-context
     (testing "Element macros work without execution context (simple mode)"
       ;; This tests that el/div etc. produce valid vnodes without context
       (let [vdom (el/div {:class "test"}
                    (el/h1 "Title")
                    (el/p "Content"))]
         (is (= :div (:tag vdom)))
         (is (= {:class "test"} @(:attrs vdom)))
         (is (= 2 (count @(:children vdom))))))))

#?(:clj
   (deftest test-nested-elements-no-context
     (testing "Nested elements work without execution context"
       (let [vdom (el/ul {:class "list"}
                    (el/li {:key "1"} "Item 1")
                    (el/li {:key "2"} "Item 2")
                    (el/li {:key "3"} "Item 3"))]
         (is (= :ul (:tag vdom)))
         (is (= 3 (count @(:children vdom))))
         (is (= "1" (:key (first @(:children vdom)))))))))
