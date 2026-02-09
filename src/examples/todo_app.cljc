(ns examples.todo-app
  "Complete Todo Application Example

  This example demonstrates the full spindel reactive programming model:

  1. **Signals** - Mutable reactive state (todos list)
  2. **Intervals** - Unified old/new/deltas abstraction from track
  3. **Incremental Combinators** - O(delta) transformations via ifilter/imap
  4. **DOM Rendering** - Reactive vdom with keyed incremental for-each

  The key insight is that everything flows through the Interval abstraction:
  - Signal changes -> Interval (via track)
  - Combinator processing -> Interval
  - DOM updates -> Uses deltas from Interval

  Usage (in CLJS with browser):
    (require '[examples.todo-app :as app])
    (app/mount! (.getElementById js/document \"app\"))

  Usage (testing with mock discharge):
    (require '[examples.todo-app :as app])
    (app/run-test-scenario!)
  "
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.incremental.combinators :refer [ifilter imap]]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.foreach :as foreach :refer [ifor-each]]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.incremental.combinators :refer [ifilter imap]]
                            [org.replikativ.spindel.dom.foreach :refer [ifor-each]])))

;; =============================================================================
;; Application State
;; =============================================================================

;; State atoms - initialized per-context
(def ^:dynamic *todos-state* nil)
(def ^:dynamic *filter-state* nil)

;; =============================================================================
;; State Initialization
;; =============================================================================

(defn make-todos-signal
  "Create a new todos signal with empty initial value."
  []
  (sig/signal []))

(defn make-filter-signal
  "Create a new filter signal with :all as default."
  []
  (sig/signal :all))

;; =============================================================================
;; Actions (State Mutations)
;; =============================================================================

(defn add-todo!
  "Add a new todo item."
  ([todos-state text]
   (add-todo! todos-state text :medium))
  ([todos-state text priority]
   (swap! todos-state conj
          {:id (str (random-uuid))
           :text text
           :done false
           :priority priority})))

(defn toggle-todo!
  "Toggle the done status of a todo by id."
  [todos-state id]
  (swap! todos-state
         (fn [todos]
           (let [idx (first (keep-indexed #(when (= (:id %2) id) %1) todos))]
             (if idx
               (assoc todos idx (update (nth todos idx) :done not))
               todos)))))

(defn remove-todo!
  "Remove a todo by id."
  [todos-state id]
  (swap! todos-state
         (fn [todos]
           ;; Find index and remove using d/remove-at
           (let [idx (first (keep-indexed #(when (= (:id %2) id) %1) todos))]
             (if idx
               (d/remove-at todos idx)
               todos)))))

(defn update-todo-text!
  "Update the text of a todo."
  [todos-state id new-text]
  (swap! todos-state
         (fn [todos]
           (let [idx (first (keep-indexed #(when (= (:id %2) id) %1) todos))]
             (if idx
               (assoc todos idx (assoc (nth todos idx) :text new-text))
               todos)))))

(defn set-filter!
  "Set the current filter mode."
  [filter-state mode]
  (reset! filter-state mode))

(defn clear-completed!
  "Remove all completed todos."
  [todos-state]
  (swap! todos-state
         (fn [todos]
           ;; Use d/filter-vec to properly track :remove deltas
           (d/filter-vec #(not (:done %)) todos))))

;; =============================================================================
;; UI Components (Pure Functions -> VNode)
;; =============================================================================

(defn todo-item
  "Render a single todo item.

  This is called by the keyed for-each combinator.
  Only called for items that actually changed (O(delta))."
  [todo]
  (el/li {:key (:id todo)
          :class (str "todo-item"
                      (when (:done todo) " done")
                      " priority-" (name (:priority todo)))}
    (el/input {:type "checkbox"
               :class "toggle"
               :checked (:done todo)})
    (el/span {:class "todo-text"} (:text todo))
    (el/button {:class "delete"} "x")))

(defn filter-button
  "Render a filter selection button."
  [mode current-mode label]
  (el/button {:class (str "filter-btn"
                          (when (= mode current-mode) " selected"))}
    label))

(defn stats-display
  "Render the statistics display."
  [{:keys [total active done]}]
  (el/div {:class "stats"}
    (el/span {:class "stat"} (str "Total: " total))
    (el/span {:class "stat"} (str " | Active: " active))
    (el/span {:class "stat"} (str " | Done: " done))))

(defn filter-bar
  "Render the filter selection bar."
  [current-mode]
  (el/div {:class "filter-bar"}
    (filter-button :all current-mode "All")
    (filter-button :active current-mode "Active")
    (filter-button :done current-mode "Done")))

;; =============================================================================
;; Main App Component
;; =============================================================================

(defn make-app-spin
  "Create the main application spin.

  Takes the state signals as arguments for testability.

  This demonstrates the full reactive model:
  1. Track signals to get Intervals
  2. Use incremental combinators (ifilter, ifor-each)
  3. Produce vdom that will be efficiently updated"
  [todos-state filter-state]
  (spin
    (let [;; Get Interval from signal tracking
          todos-iv (track todos-state)
          filter-mode @(track filter-state)

          ;; Apply filter - returns Interval
          visible-iv (case filter-mode
                       :all todos-iv
                       :active (ifilter #(not (:done %)) todos-iv)
                       :done (ifilter :done todos-iv)
                       todos-iv)

          ;; Compute stats from full list
          all-items @(:new todos-iv)
          stats {:total (count all-items)
                 :active (count (filter #(not (:done %)) all-items))
                 :done (count (filter :done all-items))}]

      ;; Render vdom
      (el/div {:class "todo-app"}
        (el/header {:class "app-header"}
          (el/h1 "Spindel Todo")
          (el/p {:class "subtitle"} "Incremental Reactive Programming"))

        ;; Stats section
        (stats-display stats)

        ;; Filter bar
        (filter-bar filter-mode)

        ;; Todo list - using keyed for-each for O(delta) rendering
        (el/ul {:class "todo-list"}
          ;; ifor-each takes the full Interval and returns an Interval of vnodes
          ;; Only items with deltas get re-rendered (true O(delta))
          ;; el/ul auto-derefs the Interval to get current children
          (ifor-each :id visible-iv todo-item))

        ;; Footer actions
        (when (pos? (:done stats))
          (el/footer {:class "app-footer"}
            (el/button {:class "clear-completed"}
              (str "Clear completed (" (:done stats) ")"))))))))

;; =============================================================================
;; Browser Mount (CLJS-only)
;; =============================================================================

#?(:cljs
   (defn mount!
     "Mount the todo app to a DOM container.

     Usage:
       (mount! (.getElementById js/document \"app\"))"
     [container]
     (let [todos (make-todos-signal)
           filter-sig (make-filter-signal)
           app (make-app-spin todos filter-sig)]
       (render/render-spin! container app nil)
       ;; Return state for interaction
       {:todos todos
        :filter filter-sig
        :add-todo! (partial add-todo! todos)
        :toggle-todo! (partial toggle-todo! todos)
        :remove-todo! (partial remove-todo! todos)
        :set-filter! (partial set-filter! filter-sig)
        :clear-completed! (partial clear-completed! todos)})))
