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
    (let [children (.-childNodes parent)
          child (aget children from-idx)]
      (when child
        ;; Remove from current position and insert at new position
        ;; Note: after removal, indices shift, so we need to account for that
        (.removeChild parent child)
        (let [ref-node (aget (.-childNodes parent) to-idx)]
          (if ref-node
            (.insertBefore parent child ref-node)
            (.appendChild parent child))))))

  (set-text-content! [_ el text]
    (set! (.-textContent el) text))

  (get-element [_ addr]
    (get @elements addr))

  (set-element! [_ addr el]
    (swap! elements assoc addr el)))

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
