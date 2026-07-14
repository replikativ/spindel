(ns org.replikativ.spindel.dom.browser
  "Browser discharge implementation for applying vdom to real DOM.

  Works in browser environments and with jsdom in Node.js.

  Usage:
    (def d (browser/make-dom-discharge js/document))
    (disch/render-initial! d vdom)
    ;; Later, after vdom updates:
    (disch/discharge-all! d updated-vdom)"
  (:require [clojure.string :as str]
            [org.replikativ.spindel.dom.discharge :as disch]))

;; =============================================================================
;; SVG namespace support
;; =============================================================================

(def ^:private svg-ns "http://www.w3.org/2000/svg")

;; Tags that must be created in the SVG namespace to render correctly.
;; Using document.createElement for these produces HTML elements without SVG rendering.
(def ^:private svg-tags
  #{"svg" "g" "path" "circle" "rect" "line" "ellipse" "polyline" "polygon"
    "text" "tspan" "defs" "use" "symbol" "clipPath" "linearGradient"
    "radialGradient" "stop" "animate" "filter" "foreignObject" "image"
    "marker" "mask" "pattern" "switch" "textPath" "view" "desc" "title"
    "metadata" "feBlend" "feColorMatrix" "feComposite" "feConvolveMatrix"
    "feDiffuseLighting" "feDisplacementMap" "feFlood" "feGaussianBlur"
    "feImage" "feMerge" "feMorphology" "feOffset" "feSpecularLighting"
    "feTile" "feTurbulence"})

;; =============================================================================
;; DOM Discharge Implementation
;; =============================================================================

(defrecord DOMDischarge [document elements]
  disch/PDischarge

  (create-element! [_ vnode]
    (let [tag-name (name (:tag vnode))
          el (if (contains? svg-tags tag-name)
               (.createElementNS document svg-ns tag-name)
               (.createElement document tag-name))]
      el))

  (create-text! [_ text-content]
    (.createTextNode document text-content))

  (set-attribute! [_ el attr-name attr-value]
    (let [attr-str (name attr-name)
          value-str (if (string? attr-value)
                      attr-value
                      (str attr-value))]
      (cond
        ;; Handle event handlers (on-click, on-change, etc. with hyphen)
        (and (keyword? attr-name)
             (str/starts-with? attr-str "on-"))
        (let [event-name (subs attr-str 3)]  ; Remove "on-" prefix
          (aset el (str "on" event-name) attr-value))

        ;; Handle event handlers (onclick, onchange, etc. without hyphen)
        (and (keyword? attr-name)
             (str/starts-with? attr-str "on")
             (fn? attr-value))
        (aset el attr-str attr-value)

        ;; Handle className specially
        (= attr-name :class)
        (.setAttribute el "class" value-str)

        ;; Handle style maps: {:height "227px" :max-width "50%"} →
        ;; "height: 227px; max-width: 50%". Without this branch a map
        ;; falls through to :else and setAttribute receives the EDN
        ;; string, which the browser silently rejects — :style maps
        ;; never render. String styles pass through :else unchanged.
        (and (= attr-name :style) (map? attr-value))
        (.setAttribute el "style"
                       (->> attr-value
                            (map (fn [[k v]] (str (name k) ": " v)))
                            (str/join "; ")))

        ;; Handle innerHTML (raw HTML injection — use with trusted content only)
        (= attr-name :innerHTML)
        (set! (.-innerHTML el) attr-value)

        ;; Handle value/checked properties (for input, select, textarea)
        ;; These must be set as DOM properties, not HTML attributes
        (= attr-name :value)
        (set! (.-value el) value-str)

        (= attr-name :checked)
        (set! (.-checked el) (boolean attr-value))

        ;; Handle boolean attributes
        (boolean? attr-value)
        (if attr-value
          (.setAttribute el attr-str "")
          (.removeAttribute el attr-str))

        ;; Standard attributes
        :else
        (.setAttribute el attr-str value-str))))

  (remove-attribute! [_ el attr-name]
    (let [attr-str (name attr-name)]
      (cond
        ;; Event handler removal
        (and (keyword? attr-name)
             (str/starts-with? attr-str "on-"))
        (let [event-name (subs attr-str 3)]
          (aset el (str "on" event-name) nil))

        ;; innerHTML removal
        (= attr-name :innerHTML)
        (set! (.-innerHTML el) "")

        ;; Standard attribute removal
        :else
        (.removeAttribute el attr-str))))

  (append-child! [_ parent child]
    (.appendChild parent child))

  (insert-child! [_ parent child index]
    (let [children (.-childNodes parent)
          ref-node (aget children index)]
      (if ref-node
        (.insertBefore parent child ref-node)
        (.appendChild parent child))))

  (remove-child! [_ parent index]
    (let [children (.-childNodes parent)
          child (aget children index)]
      (when child
        (.removeChild parent child))))

  (replace-child! [_ parent new-child index]
    (let [children (.-childNodes parent)
          old-child (aget children index)]
      (if old-child
        (.replaceChild parent new-child old-child)
        (.appendChild parent new-child))))

  (move-child! [_ parent from-idx to-idx]
    ;; `moveBefore` MOVES a node; removeChild+insertBefore DESTROYS AND RECREATES
    ;; it. For most elements the difference is invisible. For anything holding
    ;; state OUTSIDE the element — an <iframe>'s browsing context, a <video>'s
    ;; live srcObject, a WebGL context, an editor's selection — the difference is
    ;; the whole ballgame: removal runs the DOM "removing steps", which discard
    ;; that state. A Jitsi call died on a mere SIBLING REORDER, having survived
    ;; nothing more than being renumbered.
    ;;
    ;; Measured in Chromium (a counter living inside the iframe's document):
    ;;   removeChild + insertBefore → counter reset (context discarded)
    ;;   moveBefore                 → counter preserved, across reorder AND
    ;;                                across a change of parent
    ;;
    ;; moveBefore throws HierarchyRequestError if either node is DISCONNECTED,
    ;; so the fallback is not decoration: it is the path for pre-2025 browsers
    ;; (Chrome <133, Firefox/Safari until they ship it) and for any move
    ;; involving a detached tree. There, state loss is unavoidable — the platform
    ;; offers no other way — and we take the old behaviour rather than throw.
    (let [children (.-childNodes parent)
          child    (aget children from-idx)]
      (when (and child (not= from-idx to-idx))
        ;; INDEX SUBTLETY. Both APIs mean "put child before ref", and the final
        ;; index of child is ref's index in the list WITHOUT child. The old code
        ;; removed first, so it could just read the shortened list. moveBefore is
        ;; ATOMIC — the child is still present when we pick ref — so we must
        ;; account for the shift ourselves:
        ;;   moving RIGHT (to > from): everything past `from` shifts left by one
        ;;     when child leaves, so ref must be the node AFTER the target slot.
        ;;   moving LEFT  (to < from): indices below `from` are unaffected.
        ;; Getting this wrong is an off-by-one that silently misorders lists.
        (let [ref (if (< from-idx to-idx)
                    (aget children (inc to-idx))    ; may be undefined ⇒ to the end
                    (aget children to-idx))
              fallback! (fn []
                          (.removeChild parent child)
                          (let [r (aget (.-childNodes parent) to-idx)]
                            (if r
                              (.insertBefore parent child r)
                              (.appendChild parent child))))]
          (if (and (.-moveBefore parent) (.-isConnected child))
            (try
              (.moveBefore parent child (or ref nil))   ; null ⇒ append
              (catch :default _
                ;; disconnected / cross-document — the platform offers no
                ;; state-preserving path here, so take the lossy one
                (fallback!)))
            (fallback!))))))

  (child-index-of [_ parent child]
    (let [children (.-childNodes parent)
          n        (.-length children)]
      (loop [i 0]
        (cond
          (>= i n)                              nil
          (identical? child (aget children i))  i
          :else                                  (recur (inc i))))))

  (set-text-content! [_ el text]
    (set! (.-textContent el) text))

  (get-element [_ addr]
    (get @elements addr))

  (set-element! [_ addr el]
    (swap! elements assoc addr el))

  (remove-element! [_ addr]
    (swap! elements dissoc addr)))

;; =============================================================================
;; Constructor
;; =============================================================================

(defn make-dom-discharge
  "Create a DOM discharge for a document.

  In browser: (make-dom-discharge js/document)
  In jsdom: (make-dom-discharge (.-document (JSDOM. \"<html>...</html>\")))"
  [document]
  (->DOMDischarge document (atom {})))

;; =============================================================================
;; Convenience Functions
;; =============================================================================

(defn mount!
  "Mount vdom tree to a container element.

  Returns the discharge for later updates."
  [container vdom]
  (let [doc (.-ownerDocument container)
        discharge (make-dom-discharge doc)
        root-el (binding [disch/*rendered-addrs* (atom {})]
                  (disch/render-initial! discharge vdom))]
    (when root-el
      (.appendChild container root-el))
    discharge))

(defn refresh!
  "Update the DOM tree with new vdom.

   discharge: The discharge returned from mount!
   new-vdom: The updated virtual DOM tree

   This diffs the new vdom against the previous state and applies
   only the necessary changes to the DOM."
  [discharge new-vdom]
  (disch/discharge-all! discharge new-vdom))

(defn unmount!
  "Unmount a vdom tree from the DOM.

   discharge: The discharge returned from mount!

   Clears the element tracking. The actual DOM elements remain
   in place - caller should remove the container if needed."
  [discharge]
  (reset! (:elements discharge) {}))

(defn get-html
  "Get the innerHTML of an element (useful for testing)."
  [el]
  (.-innerHTML el))

(defn get-outer-html
  "Get the outerHTML of an element (useful for testing)."
  [el]
  (.-outerHTML el))
