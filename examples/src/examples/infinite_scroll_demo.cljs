(ns examples.infinite-scroll-demo
  "Infinite scroll demo showcasing O(delta) virtual list rendering with islice.

   This demo shows:
   1. Virtual list with 10,000 items but only ~10 rendered at once
   2. Scroll events produce O(delta) DOM updates via islice
   3. Window changes only touch entering/exiting items
   4. Full integration of incremental combinators with DOM rendering

   Key insight: Each scroll operation only produces deltas for items
   entering and exiting the visible window - NOT a full re-render."
  (:require [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.browser :as browser]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.incremental.combinators :as ic]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.addressing]
            [org.replikativ.spindel.spin.core]
            [is.simm.partial-cps.async])
  (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                   [org.replikativ.spindel.signal :refer [signal]]
                   [org.replikativ.spindel.incremental.combinators :refer [islice]]
                   [org.replikativ.spindel.dom.foreach :refer [ifor-each]]
                   [org.replikativ.spindel.dom.elements :as el]))

;; =============================================================================
;; Constants
;; =============================================================================

(def ^:const ITEM_HEIGHT 60)
(def ^:const VISIBLE_ITEMS 10)
(def ^:const OVERSCAN 2)
(def ^:const INITIAL_ITEMS 10000)

;; =============================================================================
;; State
;; =============================================================================

(defonce runtime (ctx/create-execution-context))

;; Signals - using signal macro with explicit runtime context for top-level definitions
;; The signal macro generates deterministic IDs via addressing chain.
;; State is cached in the runtime, so `def` (not `defonce`) is correct.
(def items-signal (signal runtime []))
(def window-signal (signal runtime {:start 0 :end (+ VISIBLE_ITEMS (* 2 OVERSCAN))}))
(defonce op-log (atom []))
(defonce render-handle (atom nil))
(defonce total-ops (atom 0))

;; =============================================================================
;; Data Generation
;; =============================================================================

(def colors
  ["#e91e63" "#9c27b0" "#673ab7" "#3f51b5" "#2196f3"
   "#00bcd4" "#009688" "#4caf50" "#8bc34a" "#ff9800"])

(def first-names
  ["Alice" "Bob" "Charlie" "Diana" "Eve" "Frank" "Grace"
   "Henry" "Iris" "Jack" "Kate" "Liam" "Mia" "Noah"])

(def last-names
  ["Smith" "Johnson" "Williams" "Brown" "Jones" "Garcia"
   "Miller" "Davis" "Rodriguez" "Martinez" "Anderson"])

(defn generate-item [id]
  (let [first-name (nth first-names (mod id (count first-names)))
        last-name (nth last-names (mod (quot id (count first-names)) (count last-names)))]
    {:id id
     :name (str first-name " " last-name)
     :email (str (.toLowerCase first-name) "." (.toLowerCase last-name) id "@example.com")
     :color (nth colors (mod id (count colors)))
     :created-at (+ 1700000000000 (* id 1000))}))

(defn generate-items [n]
  (vec (map generate-item (range n))))

;; =============================================================================
;; Logging Discharge
;; =============================================================================

(defrecord LoggingDischarge [inner log]
  disch/PDischarge

  (create-element! [_ vnode]
    (swap! log conj {:op :create :tag (:tag vnode) :type :add})
    (swap! total-ops inc)
    (disch/create-element! inner vnode))

  (create-text! [_ text]
    (swap! log conj {:op :create-text :text (subs (str text) 0 (min 20 (count (str text)))) :type :add})
    (swap! total-ops inc)
    (disch/create-text! inner text))

  (set-attribute! [_ el attr-name attr-value]
    (disch/set-attribute! inner el attr-name attr-value))

  (remove-attribute! [_ el attr-name]
    (disch/remove-attribute! inner el attr-name))

  (append-child! [_ parent child]
    (swap! log conj {:op :append :type :add})
    (swap! total-ops inc)
    (disch/append-child! inner parent child))

  (insert-child! [_ parent child index]
    (swap! log conj {:op :insert :index index :type :add})
    (swap! total-ops inc)
    (disch/insert-child! inner parent child index))

  (remove-child! [_ parent index]
    (swap! log conj {:op :remove :index index :type :remove})
    (swap! total-ops inc)
    (disch/remove-child! inner parent index))

  (replace-child! [_ parent new-child index]
    (swap! log conj {:op :replace :index index :type :add})
    (swap! total-ops inc)
    (disch/replace-child! inner parent new-child index))

  (set-text-content! [_ el text]
    (disch/set-text-content! inner el text))

  (get-element [_ vnode]
    (disch/get-element inner vnode))

  (set-element! [_ vnode el]
    (disch/set-element! inner vnode el))

  (remove-children-range! [this parent start-idx cnt]
    (swap! log conj {:op :remove-range :start start-idx :count cnt :type :remove})
    (swap! total-ops inc)
    (disch/remove-children-range! inner parent start-idx cnt))

  (insert-children! [this parent children start-idx]
    (swap! log conj {:op :insert-children :start start-idx :count (count children) :type :add})
    (swap! total-ops inc)
    (disch/insert-children! inner parent children start-idx)))

(defn make-logging-discharge [document log]
  (->LoggingDischarge (browser/make-dom-discharge document) log))

;; =============================================================================
;; Item Rendering
;; =============================================================================

(defn render-list-item [item]
  (let [initials (str (first (:name item)) (first (second (.split (:name item) " "))))]
    ;; Items are positioned by the parent container's translateY
    ;; Don't add individual transforms - items flow naturally in document order
    (el/div {:key (str (:id item))
             :class "list-item"}
      (el/span {:class "item-index"} (str "#" (:id item)))
      (el/div {:class "item-avatar"
               :style (str "background: " (:color item))}
        initials)
      (el/div {:class "item-content"}
        (el/div {:class "item-name"} (:name item))
        (el/div {:class "item-email"} (:email item)))
      (el/div {:class "item-meta"}
        (str "ID: " (:id item))))))

;; =============================================================================
;; Window Calculation
;; =============================================================================

(defn compute-window [scroll-top total-items]
  (let [start-idx (max 0 (- (quot scroll-top ITEM_HEIGHT) OVERSCAN))
        end-idx (min total-items (+ start-idx VISIBLE_ITEMS (* 2 OVERSCAN)))]
    {:start start-idx :end end-idx}))

;; =============================================================================
;; App Spin
;; =============================================================================

(defn make-app-spin [items-sig window-sig]
  (spin
    (let [;; Track both signals - returns Intervals
          ;; NOTE: track is a suspension point - spin may be re-entered here
          ;; So we measure time AFTER track to get accurate post-suspension timing
          items-iv (track items-sig)

          ;; Measure time starting from AFTER first track (when spin actually resumes)
          t-start (js/performance.now)

          window-iv (track window-sig)
          t-window (js/performance.now)

          ;; Get current values from intervals
          all-items (:new items-iv)
          window (:new window-iv)
          start (:start window)

          ;; Apply slice to get visible window with O(delta) updates
          visible-iv (islice window items-iv)
          t-slice (js/performance.now)

          ;; Debug: log islice deltas
          _ (when-let [deltas (:deltas visible-iv)]
              (js/console.log "islice deltas:" (pr-str deltas))
              (js/console.log "visible-iv :new items:" (mapv :id (:new visible-iv))))

          ;; Calculate total height for scroll spacer
          total-height (* (count all-items) ITEM_HEIGHT)]

      ;; Render virtual list structure - time this separately
      (let [t-pre-render (js/performance.now)
            result (el/div {:class "scroll-spacer"
                            :style (str "height: " total-height "px")}
                     (el/div {:class "visible-items"
                              :style (str "transform: translateY(" (* start ITEM_HEIGHT) "px)")}
                       (ifor-each :id visible-iv render-list-item)))
            t-post-render (js/performance.now)
            delta-count (count (:deltas visible-iv))]
        (js/console.log (str "[" (.toFixed t-post-render 0) "ms] SPIN: "
                             "window-track=" (.toFixed (- t-window t-start) 1) "ms, "
                             "islice=" (.toFixed (- t-slice t-window) 1) "ms, "
                             "render=" (.toFixed (- t-post-render t-pre-render) 1) "ms, "
                             "TOTAL=" (.toFixed (- t-post-render t-start) 1) "ms, "
                             "deltas=" delta-count))
        result))))

;; =============================================================================
;; UI Updates
;; =============================================================================

(defn format-op [{:keys [op type] :as entry}]
  (let [class-name (if (= type :add) "add" "remove")]
    (str "<div class=\"log-entry " class-name "\">"
         (case op
           :create (str "+ CREATE <" (name (:tag entry)) ">")
           :create-text (str "+ TEXT \"" (:text entry) "\"")
           :append "+ APPEND"
           :insert (str "+ INSERT @" (:index entry))
           :remove (str "- REMOVE @" (:index entry))
           :replace (str "+ REPLACE @" (:index entry))
           (str op))
         "</div>")))

(defn update-log-display! []
  (when-let [log-el (js/document.getElementById "op-log")]
    (let [ops @op-log
          recent (take-last 100 ops)]
      (if (empty? recent)
        (set! (.-innerHTML log-el) "<em>No operations yet</em>")
        (set! (.-innerHTML log-el)
              (->> recent
                   reverse
                   (map format-op)
                   (apply str)))))))

(defn update-stats-display! []
  (binding [ec/*execution-context* runtime]
    (let [items @items-signal
          window @window-signal]
      ;; Update metrics
      (when-let [el (js/document.getElementById "total-items")]
        (set! (.-textContent el) (str (count items))))
      (when-let [el (js/document.getElementById "visible-count")]
        (set! (.-textContent el) (str (- (:end window) (:start window)))))
      (when-let [el (js/document.getElementById "dom-ops")]
        (set! (.-textContent el) (str @total-ops)))
      ;; Update stats line
      (when-let [el (js/document.getElementById "render-stats")]
        (set! (.-innerHTML el)
              (str "<strong>Window:</strong> [" (:start window) ", " (:end window) ") | "
                   "<strong>Total:</strong> " (count items) " | "
                   "<strong>DOM Ops:</strong> " @total-ops))))))

;; =============================================================================
;; Actions
;; =============================================================================

(defn update-window! [scroll-top]
  (let [t0 (js/performance.now)]
    (binding [ec/*execution-context* runtime]
      (let [items @items-signal
            new-window (compute-window scroll-top (count items))
            old-window @window-signal]
        ;; Only update if window actually changed
        (when (not= old-window new-window)
          (js/console.log (str "[" (.toFixed t0 0) "ms] SCROLL: " (:start old-window) "->" (:start new-window)))
          (reset! window-signal new-window))))))

(defn scroll-to! [position]
  (let [container (js/document.getElementById "scroll-container")]
    (set! (.-scrollTop container) position)
    (update-window! position)))

(defn scroll-by! [delta]
  (let [container (js/document.getElementById "scroll-container")
        current (.-scrollTop container)
        new-pos (max 0 (+ current delta))]
    (set! (.-scrollTop container) new-pos)
    (reset! op-log [])
    (update-window! new-pos)
    (js/setTimeout update-log-display! 50)
    (js/setTimeout update-stats-display! 50)))

(defn jump-to-index! [idx]
  (reset! op-log [])
  (let [scroll-pos (* idx ITEM_HEIGHT)]
    (scroll-to! scroll-pos)
    (js/setTimeout update-log-display! 50)
    (js/setTimeout update-stats-display! 50)))

(defn add-items! [n]
  (reset! op-log [])
  (binding [ec/*execution-context* runtime]
    (let [current-items @items-signal
          current-count (count current-items)
          new-items (vec (concat current-items
                                 (map #(generate-item (+ current-count %)) (range n))))]
      (reset! items-signal new-items)))
  (js/setTimeout update-log-display! 50)
  (js/setTimeout update-stats-display! 50))

(defn remove-items! [n]
  (reset! op-log [])
  (binding [ec/*execution-context* runtime]
    (let [current-items @items-signal
          new-count (max 0 (- (count current-items) n))]
      (reset! items-signal (subvec current-items 0 new-count))))
  (js/setTimeout update-log-display! 50)
  (js/setTimeout update-stats-display! 50))

(defn reset-items! []
  (reset! op-log [])
  (reset! total-ops 0)
  (binding [ec/*execution-context* runtime]
    (reset! items-signal (generate-items INITIAL_ITEMS))
    (reset! window-signal {:start 0 :end VISIBLE_ITEMS}))
  (scroll-to! 0)
  (js/setTimeout update-log-display! 50)
  (js/setTimeout update-stats-display! 50))

;; =============================================================================
;; Event Setup
;; =============================================================================

(defn setup-scroll-handler! []
  (let [container (js/document.getElementById "scroll-container")]
    (.addEventListener container "scroll"
      (fn [_e]
        (let [scroll-top (.-scrollTop container)]
          (reset! op-log [])
          (update-window! scroll-top)
          (js/setTimeout update-log-display! 20)
          (js/setTimeout update-stats-display! 20))))))

(defn setup-button-handlers! []
  ;; Scroll controls
  (when-let [btn (js/document.getElementById "btn-scroll-down")]
    (.addEventListener btn "click"
      (fn [_] (scroll-by! (* 5 ITEM_HEIGHT)))))

  (when-let [btn (js/document.getElementById "btn-scroll-up")]
    (.addEventListener btn "click"
      (fn [_] (scroll-by! (* -5 ITEM_HEIGHT)))))

  (when-let [btn (js/document.getElementById "btn-scroll-page")]
    (.addEventListener btn "click"
      (fn [_] (scroll-by! (* VISIBLE_ITEMS ITEM_HEIGHT)))))

  ;; Jump controls
  (when-let [btn (js/document.getElementById "btn-jump-start")]
    (.addEventListener btn "click"
      (fn [_] (jump-to-index! 0))))

  (when-let [btn (js/document.getElementById "btn-jump-middle")]
    (.addEventListener btn "click"
      (fn [_]
        (binding [ec/*execution-context* runtime]
          (let [mid (quot (count @items-signal) 2)]
            (jump-to-index! mid))))))

  (when-let [btn (js/document.getElementById "btn-jump-end")]
    (.addEventListener btn "click"
      (fn [_]
        (binding [ec/*execution-context* runtime]
          (let [end-idx (- (count @items-signal) VISIBLE_ITEMS)]
            (jump-to-index! end-idx))))))

  (when-let [btn (js/document.getElementById "btn-jump-random")]
    (.addEventListener btn "click"
      (fn [_]
        (binding [ec/*execution-context* runtime]
          (let [max-idx (- (count @items-signal) VISIBLE_ITEMS)
                rand-idx (rand-int max-idx)]
            (jump-to-index! rand-idx))))))

  ;; Data controls
  (when-let [btn (js/document.getElementById "btn-add-items")]
    (.addEventListener btn "click"
      (fn [_] (add-items! 100))))

  (when-let [btn (js/document.getElementById "btn-remove-items")]
    (.addEventListener btn "click"
      (fn [_] (remove-items! 100))))

  (when-let [btn (js/document.getElementById "btn-reset")]
    (.addEventListener btn "click"
      (fn [_] (reset-items!)))))

;; =============================================================================
;; Initialization
;; =============================================================================

(defn ^:export init []
  (js/console.log "Initializing Infinite Scroll demo...")

  ;; Reset signal values for hot reload
  (binding [ec/*execution-context* runtime]
    (reset! items-signal (generate-items INITIAL_ITEMS))
    (reset! window-signal {:start 0 :end (+ VISIBLE_ITEMS (* 2 OVERSCAN))}))

  ;; Get container and set up rendering
  (let [container (js/document.getElementById "scroll-container")
        discharge (make-logging-discharge js/document op-log)]

    ;; Set up reactive rendering - pass SignalRefs directly (make-app-spin tracks them)
    (binding [ec/*execution-context* runtime]
      (let [app-spin (make-app-spin items-signal window-signal)]
        (reset! render-handle
                (render/render-spin! container app-spin discharge))))

    ;; Set up event handlers
    (setup-scroll-handler!)
    (setup-button-handlers!)

    ;; Initial display update
    (js/setTimeout update-stats-display! 100)

    (js/console.log "Infinite Scroll demo initialized with" INITIAL_ITEMS "items")))
