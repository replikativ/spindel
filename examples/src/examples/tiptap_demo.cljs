(ns examples.tiptap-demo
  "Simple TipTap demo using spindel's foreign-node primitive.

   This demonstrates integrating TipTap directly with spindel (no React wrapper).
   The foreign-node creates a container whose children TipTap manages."
  (:require [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.browser :as browser]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.foreign :as foreign]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.addressing]
            [org.replikativ.spindel.spin.core]
            [is.simm.partial-cps.async]
            ["@tiptap/core" :refer [Editor]]
            ["@tiptap/starter-kit" :default StarterKit])
  (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                   [org.replikativ.spindel.signal :refer [signal]]
                   [org.replikativ.spindel.dom.foreign :refer [foreign-node]]
                   [org.replikativ.spindel.dom.elements :as el]))

;; =============================================================================
;; State
;; =============================================================================

(defonce runtime (ctx/create-execution-context))

;; Content signal - using signal macro with explicit runtime context for top-level definitions.
;; The signal macro generates deterministic IDs via addressing chain.
;; State is cached in the runtime, so `def` (not `defonce`) is correct.
;; SignalRef implements IAtom so we can use swap!/reset! directly.
(def content-sig (signal runtime "<p>Hello, this is a <strong>TipTap</strong> editor!</p>"))

;; Atom to hold editor instance for cleanup (JS object, not reactive data)
(defonce editor-atom (atom nil))

;; =============================================================================
;; TipTap Editor Component
;; =============================================================================

(defn create-editor!
  "Create and mount a TipTap editor to the given DOM element.
   Updates the content signal when editor content changes."
  [element content-signal]
  (js/console.log "Creating TipTap editor on element:" element)

  (let [editor (Editor.
                 #js {:element element
                      :extensions #js [(.configure StarterKit #js {})]
                      :content @content-signal
                      :onUpdate (fn [^js props]
                                  (let [html (.getHTML (.-editor props))]
                                    (js/console.log "Editor updated, HTML length:" (count html))
                                    ;; Update signal - needs execution context bound
                                    (binding [ec/*execution-context* runtime]
                                      (reset! content-signal html))))})]
    (js/console.log "TipTap editor created successfully")
    (reset! editor-atom editor)
    editor))

(defn destroy-editor!
  "Destroy the TipTap editor and clean up."
  []
  (when-let [editor @editor-atom]
    (js/console.log "Destroying TipTap editor")
    (.destroy editor)
    (reset! editor-atom nil)))

;; =============================================================================
;; App Spin (Main Reactive Component)
;; =============================================================================

(defn make-app-spin [content-signal]
  (spin
    ;; Track the content signal for reactive updates
    (let [content @(track content-signal)
          ;; Truncate for display if too long
          display-html (if (> (count content) 500)
                         (str (subs content 0 500) "...")
                         content)]

      (el/div {:class "tiptap-demo"}
        ;; Header
        (el/header {:class "demo-header"}
          (el/h1 "TipTap + Spindel Demo")
          (el/p {:class "subtitle"}
            "Using foreign-node to integrate TipTap with spindel's VDOM"))

        ;; Editor container using foreign-node
        (el/div {:class "editor-section"}
          (el/h2 "Editor")
          (foreign-node
            {:class "tiptap-editor"
             :on-mount (fn [el]
                         (create-editor! el content-signal))
             :on-unmount (fn [_]
                           (destroy-editor!))}))

        ;; Live preview of content - now reactively updated via signal
        (el/div {:class "preview-section"}
          (el/h2 "Content (HTML)")
          (el/pre {:class "content-preview"}
            (el/code display-html)))

        ;; Instructions
        (el/div {:class "stats-section"}
          (el/h3 "How it works")
          (el/p "The TipTap editor is mounted inside a 'foreign-node' - a spindel container whose children are managed by TipTap (ProseMirror), not by spindel's VDOM.")
          (el/p "Try typing, formatting with Ctrl+B/I, or creating lists!"))))))

;; =============================================================================
;; Main App Setup
;; =============================================================================

(defn ^:export init []
  (js/console.log "Initializing TipTap demo...")

  ;; Get container
  (let [container (js/document.getElementById "app")
        discharge (browser/make-dom-discharge js/document)]

    (when-not container
      (js/console.error "Container #app not found!")
      (throw (js/Error. "Container #app not found")))

    ;; Set up reactive rendering
    (js/console.log "Setting up reactive rendering...")
    (try
      (binding [ec/*execution-context* runtime]
        ;; Pass content signal to the app spin for reactive tracking
        (let [app-spin (make-app-spin content-sig)]
          (js/console.log "App spin created, starting render...")
          (render/render-spin! container app-spin discharge)))
      (catch :default e
        (js/console.error "ERROR in rendering:" e)
        (js/console.error "Error stack:" (.-stack e))))

    (js/console.log "TipTap demo initialized!")))
