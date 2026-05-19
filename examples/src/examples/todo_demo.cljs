(ns examples.todo-demo
  "TODO MVC-like demo for testing spindel incremental DOM rendering.

   This demo tests:
   1. Add/remove items (structural changes)
   2. Toggle done status (attribute updates via class changes)
   3. Edit item text (text node updates)
   4. Filtering with ifilter (reactive filtering)
   5. Priority changes (nested element structure)

   All with O(delta) incremental updates - only changed DOM nodes are touched."
  (:require [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.incremental.combinators :refer [filter*]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.addressing]  ;; Required by spin macro expansion
            [org.replikativ.spindel.spin.core]           ;; Required by spin macro expansion
            [is.simm.partial-cps.async]                  ;; Required by spin macro expansion
            [examples.shared.logging-discharge :as logging])
  (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                   [org.replikativ.spindel.signal :refer [signal]]
                   [org.replikativ.spindel.incremental.combinators :refer [ifilter]]
                   [org.replikativ.spindel.dom.foreach :refer [ifor-each]]
                   [org.replikativ.spindel.dom.elements :as el]))

;; =============================================================================
;; State
;; =============================================================================

(defonce runtime (ctx/create-execution-context))

;; Signals - using signal macro with explicit runtime context for top-level definitions
;; The signal macro generates deterministic IDs via addressing chain.
;; State is cached in the runtime, so `def` (not `defonce`) is correct.
(def todos-signal (signal runtime (d/deltaable-vector [])))
(def filter-signal (signal runtime :all))
(defonce counter (atom 0))
(defonce op-log (atom []))
(defonce render-handle (atom nil))

;; LoggingDischarge lives in examples.shared.logging-discharge — same
;; deftype is used by todo, infinite-scroll, and block-editor.

;; =============================================================================
;; Todo Item Structure
;; =============================================================================

;; Each todo: {:id uuid :text string :done boolean :priority :low/:medium/:high}

;; Stable filter predicates (avoid creating new fns on each render)
(def active-pred (fn [todo] (not (:done todo))))
(def done-pred (fn [todo] (:done todo)))

(def priority-colors
  {:low "#e8f5e9"      ;; light green
   :medium "#fff3e0"   ;; light orange
   :high "#ffebee"})   ;; light red

(def priority-order [:low :medium :high])

;; =============================================================================
;; Actions (State Mutations)
;; =============================================================================

(defn add-todo! [text priority]
  (let [id (swap! counter inc)]
    (swap! todos-signal conj
           {:id id
            :text text
            :done false
            :priority (or priority :medium)})
    (js/console.log "Added todo" id)))

(defn toggle-todo! [id]
  (swap! todos-signal d/update-by-key :id id update :done not)
  (js/console.log "Toggled todo" id))

(defn remove-todo! [id]
  (swap! todos-signal
         (fn [todos]
           (if-let [idx (d/find-index #(= (:id %) id) todos)]
             (d/remove-at todos idx)
             todos)))
  (js/console.log "Removed todo" id))

(defn update-todo-text! [id new-text]
  (swap! todos-signal d/update-by-key :id id assoc :text new-text)
  (js/console.log "Updated todo text" id))

(defn cycle-priority! [id]
  (swap! todos-signal
         d/update-by-key :id id
         (fn [todo]
           (let [current-idx (.indexOf (to-array priority-order) (:priority todo))
                 next-idx (mod (inc current-idx) (count priority-order))]
             (assoc todo :priority (nth priority-order next-idx)))))
  (js/console.log "Cycled priority for" id))

(defn set-filter! [mode]
  (reset! filter-signal mode)
  (js/console.log "Set filter to" mode))

(defn clear-completed! []
  (swap! todos-signal
         (fn [todos]
           (d/filter-vec #(not (:done %)) todos)))
  (js/console.log "Cleared completed"))

;; =============================================================================
;; Todo Item Rendering
;; =============================================================================

(defn render-todo-item [todo]
  (el/li {:key (str (:id todo))
          :class (str "todo-item"
                      (when (:done todo) " done"))
          :style (str "background: " (get priority-colors (:priority todo) "#fff"))}
    ;; Checkbox for toggle
    (el/input {:type "checkbox"
               :class "todo-toggle"
               :checked (:done todo)
               :data-id (str (:id todo))})
    ;; Todo text
    (el/span {:class (str "todo-text" (when (:done todo) " completed"))}
      (:text todo))
    ;; Priority badge
    (el/span {:class (str "priority-badge " (name (:priority todo)))
              :data-id (str (:id todo))}
      (name (:priority todo)))
    ;; Delete button
    (el/button {:class "todo-delete"
                :data-id (str (:id todo))}
      "×")))

;; =============================================================================
;; App Spin (Main Reactive Component)
;; =============================================================================

(defn make-app-spin [todos-sig filter-sig]
  (spin
    (let [_ (js/console.log "make-app-spin body executing...")
          _ (js/console.log "todos-sig:" todos-sig)
          _ (js/console.log "filter-sig:" filter-sig)
          ;; Track signals to get intervals
          _ (js/console.log "About to track todos-sig...")
          todos-iv (track todos-sig)
          _ (js/console.log "todos-iv:" todos-iv)
          _ (js/console.log "About to track filter-sig...")
          filter-mode (iv/get-new (track filter-sig))
          _ (js/console.log "filter-mode:" filter-mode)

          ;; Apply filter using ifilter combinator
          ;; Use stable predicates to enable cache hits when switching back
          visible-iv (case filter-mode
                       :all todos-iv
                       :active (ifilter active-pred todos-iv)
                       :done (ifilter done-pred todos-iv)
                       todos-iv)

          ;; Get current values for stats. `iv/get-new` returns the
          ;; new value of the interval (a deltaable-vector here); `@`
          ;; unwraps it to a plain Clojure vector for the (count …)s
          ;; below.
          all-items @(iv/get-new todos-iv)
          total (count all-items)
          active-count (count (filter #(not (:done %)) all-items))
          done-count (count (filter :done all-items))]

      ;; Render vdom
      (el/div {:class "todo-app"}
        ;; Header
        (el/header {:class "app-header"}
          (el/h2 "Spindel TODO MVC")
          (el/p {:class "subtitle"} "Testing O(delta) incremental rendering"))

        ;; Stats bar
        (el/div {:class "stats-bar"}
          (el/span {:class "stat"} (str "Total: " total))
          (el/span {:class "stat"} (str "Active: " active-count))
          (el/span {:class "stat"} (str "Done: " done-count)))

        ;; Filter buttons
        (el/div {:class "filter-bar"}
          (el/button {:class (str "filter-btn" (when (= filter-mode :all) " active"))
                      :data-filter "all"}
            "All")
          (el/button {:class (str "filter-btn" (when (= filter-mode :active) " active"))
                      :data-filter "active"}
            "Active")
          (el/button {:class (str "filter-btn" (when (= filter-mode :done) " active"))
                      :data-filter "done"}
            "Done"))

        ;; Todo list - using ifor-each for O(delta) rendering
        (el/ul {:class "todo-list"}
          (ifor-each :id visible-iv render-todo-item))

        ;; Footer with clear completed
        (when (pos? done-count)
          (el/footer {:class "app-footer"}
            (el/button {:class "clear-completed"
                        :id "clear-completed-btn"}
              (str "Clear completed (" done-count ")"))))))))

;; =============================================================================
;; Log Display
;; =============================================================================

(defn format-op [{:keys [op] :as entry}]
  (case op
    :create (str "CREATE <" (name (:tag entry)) ">")
    :create-text (str "TEXT \"" (:text entry) "\"")
    :set-attr (str "ATTR " (name (:attr entry)) "=" (:value entry))
    :remove-attr (str "DEL-ATTR " (name (:attr entry)))
    :append "APPEND"
    :insert (str "INSERT @" (:index entry))
    :remove (str "REMOVE @" (:index entry))
    :replace (str "REPLACE @" (:index entry))
    :set-text (str "SET-TEXT \"" (:text entry) "\"")
    (str op)))

(defn- render-log-html [ops]
  (let [recent (take-last 100 ops)]
    (if (empty? recent)
      "<em>No operations yet</em>"
      (->> recent
           reverse
           (map format-op)
           (map #(str "<div class=\"log-entry\">" % "</div>"))
           (apply str)))))

;; --- Reactive panels ------------------------------------------------------
;;
;; The op-log panel is driven by a `add-watch` on the plain `op-log` atom.
;; The discharge mutates op-log many times per render, so a per-mutation
;; redraw would be wasteful; we coalesce updates through a microtask gate
;; (`log-panel-pending?`) so the panel redraws once per JS turn no matter
;; how many ops landed.
;;
;; The stats panel is a spin that tracks `todos-signal` + `filter-signal`.
;; The op-count it shows is read non-reactively from `@op-log` — that's
;; fine because every action that changes op-log also changes one of the
;; tracked signals.

(defonce log-panel-pending? (atom false))

(defn- refresh-log-panel! []
  (when-let [log-el (js/document.getElementById "op-log")]
    (set! (.-innerHTML log-el) (render-log-html @op-log))))

(add-watch op-log ::panel
  (fn [_ _ _ _]
    (when (compare-and-set! log-panel-pending? false true)
      (js/queueMicrotask
        (fn []
          (reset! log-panel-pending? false)
          (refresh-log-panel!))))))

(defn make-stats-spin [todos-sig filter-sig]
  (spin
    (let [todos (iv/get-new (track todos-sig))
          fm (iv/get-new (track filter-sig))]
      (when-let [stats-el (js/document.getElementById "render-stats")]
        (set! (.-textContent stats-el)
              (str "Items: " (count todos)
                   " | Filter: " (name fm)
                   " | Ops: " (count @op-log))))
      nil)))

(defonce stats-spin-handle (atom nil))

;; =============================================================================
;; Event Delegation
;; =============================================================================

(defn handle-list-click
  "Handle clicks in the todo list container.
   Assumes *execution-context* is bound."
  [e]
  (let [target (.-target e)
        classList (.-classList target)]
    (reset! op-log [])
    (cond
      ;; Toggle checkbox
      (.contains classList "todo-toggle")
      (let [id (js/parseInt (.-id (.-dataset target)))]
        (toggle-todo! id))

      ;; Delete button
      (.contains classList "todo-delete")
      (let [id (js/parseInt (.-id (.-dataset target)))]
        (remove-todo! id))

      ;; Priority badge (cycle priority)
      (.contains classList "priority-badge")
      (let [id (js/parseInt (.-id (.-dataset target)))]
        (cycle-priority! id))

      ;; Filter buttons
      (.contains classList "filter-btn")
      (let [filter-str (.-filter (.-dataset target))
            filter-mode (keyword filter-str)]
        (set-filter! filter-mode))

      ;; Clear completed
      (.contains classList "clear-completed")
      (clear-completed!))))

(defn setup-event-delegation! [container]
  ;; Use event delegation on the container with context auto-bound
  (.addEventListener container "click" (ec/make-handler runtime handle-list-click)))

;; =============================================================================
;; Button Handlers (assume *execution-context* is bound)
;; =============================================================================

(defn handle-add-todo [_]
  (reset! op-log [])
  (let [text (str "Task " (inc @counter))]
    (add-todo! text :medium))
  nil)

(defn handle-add-high [_]
  (reset! op-log [])
  (let [text (str "URGENT: Task " (inc @counter))]
    (add-todo! text :high))
  nil)

(defn handle-add-low [_]
  (reset! op-log [])
  (let [text (str "Low priority: Task " (inc @counter))]
    (add-todo! text :low))
  nil)

(defn handle-add-10 [_]
  (reset! op-log [])
  (dotimes [i 10]
    (let [priority (nth priority-order (mod i 3))
          text (str (name priority) " task " (inc @counter))]
      (add-todo! text priority)))
  nil)

(defn handle-toggle-first [_]
  (reset! op-log [])
  (when-let [first-todo (first @todos-signal)]
    (toggle-todo! (:id first-todo)))
  nil)

(defn handle-remove-first [_]
  (reset! op-log [])
  (when-let [first-todo (first @todos-signal)]
    (remove-todo! (:id first-todo)))
  nil)

(defn handle-remove-last [_]
  (reset! op-log [])
  (when-let [last-todo (last @todos-signal)]
    (remove-todo! (:id last-todo)))
  nil)

(defn handle-remove-middle [_]
  (reset! op-log [])
  (let [todos @todos-signal
        mid-idx (quot (count todos) 2)]
    (when (> (count todos) 0)
      (remove-todo! (:id (nth todos mid-idx)))))
  nil)

(defn handle-clear-all [_]
  (reset! op-log [])
  (reset! todos-signal (d/deltaable-vector []))
  (reset! counter 0)
  nil)

;; =============================================================================
;; Main App Setup
;; =============================================================================

(defn ^:export init []
  (js/console.log "Initializing TODO MVC demo...")

  ;; Reset signal values for hot reload
  ;; NOTE: Use direct `binding` form instead of `ec/with-context` because the
  ;; macro version (used in CLJS compilation) doesn't call the callback function.
  (binding [ec/*execution-context* runtime]
    (reset! todos-signal (d/deltaable-vector []))
    (reset! filter-signal :all))

  ;; Get container
  (let [container (js/document.getElementById "list-container")
        discharge (logging/make-logging-discharge js/document op-log)]

    ;; Set up reactive rendering
    ;; Pass SignalRefs (not dereferenced values) so track can work
    ;; NOTE: Use direct `binding` form instead of `ec/with-context` because the
    ;; macro version (used in CLJS compilation) doesn't call the callback function.
    (js/console.log "Setting up reactive rendering with binding...")
    (try
      (binding [ec/*execution-context* runtime]
        (js/console.log "Inside binding, context-bound?:" (ec/execution-context-bound?))
        (let [app-spin (make-app-spin todos-signal filter-signal)
              stats-spin (make-stats-spin todos-signal filter-signal)]
          (js/console.log "app-spin created:" app-spin)
          (js/console.log "About to call render-spin!...")
          (reset! render-handle
                  (render/render-spin! container app-spin discharge))
          ;; Kick the stats-spin once; track-driven self-scheduling
          ;; takes over from there. No render-spin! — it has no vnode.
          (reset! stats-spin-handle stats-spin)
          (stats-spin identity identity)
          ;; Initial paint of the log panel.
          (refresh-log-panel!)
          (js/console.log "render-spin! returned")))
      (catch :default e
        (js/console.error "ERROR in rendering:" e)
        (js/console.error "Error stack:" (.-stack e))))

    ;; Set up event delegation on list container
    (setup-event-delegation! container)

    ;; Wire up control panel buttons with auto-bound context
    (when-let [btn (js/document.getElementById "btn-add")]
      (.addEventListener btn "click" (ec/make-handler runtime handle-add-todo)))

    (when-let [btn (js/document.getElementById "btn-add-high")]
      (.addEventListener btn "click" (ec/make-handler runtime handle-add-high)))

    (when-let [btn (js/document.getElementById "btn-add-low")]
      (.addEventListener btn "click" (ec/make-handler runtime handle-add-low)))

    (when-let [btn (js/document.getElementById "btn-add-10")]
      (.addEventListener btn "click" (ec/make-handler runtime handle-add-10)))

    (when-let [btn (js/document.getElementById "btn-toggle-first")]
      (.addEventListener btn "click" (ec/make-handler runtime handle-toggle-first)))

    (when-let [btn (js/document.getElementById "btn-remove-first")]
      (.addEventListener btn "click" (ec/make-handler runtime handle-remove-first)))

    (when-let [btn (js/document.getElementById "btn-remove-last")]
      (.addEventListener btn "click" (ec/make-handler runtime handle-remove-last)))

    (when-let [btn (js/document.getElementById "btn-remove-middle")]
      (.addEventListener btn "click" (ec/make-handler runtime handle-remove-middle)))

    (when-let [btn (js/document.getElementById "btn-clear-all")]
      (.addEventListener btn "click" (ec/make-handler runtime handle-clear-all)))

    (js/console.log "TODO MVC demo initialized!")))
