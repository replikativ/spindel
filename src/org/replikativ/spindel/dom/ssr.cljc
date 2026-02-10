(ns org.replikativ.spindel.dom.ssr
  "Server-side rendering: render vdom trees to HTML strings.

  Pure functions, no execution context needed. Works with vnodes created
  by element macros in simple mode (no context) or with any vdom tree.

  Usage:
    (require '[org.replikativ.spindel.dom.ssr :as ssr])
    (require '[org.replikativ.spindel.dom.elements :as el])
    (ssr/render-to-string (el/div {:class \"app\"} (el/h1 \"Hello\")))"
  (:require [clojure.string :as str]
            [org.replikativ.spindel.dom.core :as core]
            [org.replikativ.spindel.dom.fragment :as frag]))

;; =============================================================================
;; HTML Escaping
;; =============================================================================

(defn escape-html
  "Escape HTML special characters in text content and attribute values."
  [s]
  (-> (str s)
      (str/replace "&" "&amp;")
      (str/replace "<" "&lt;")
      (str/replace ">" "&gt;")
      (str/replace "\"" "&quot;")
      (str/replace "'" "&#x27;")))

;; =============================================================================
;; Attribute Rendering
;; =============================================================================

(def ^:private void-elements
  "HTML void elements that must not have a closing tag."
  #{:area :base :br :col :embed :hr :img :input :link :meta :param :source :track :wbr})

(defn- void-element?
  [tag]
  (contains? void-elements tag))

(defn- render-attr
  "Render a single attribute key-value pair to a string.
  Returns nil for attrs that should be skipped."
  [k v]
  (cond
    (nil? v) nil
    (false? v) nil
    (fn? v) nil
    (true? v) (name k)
    :else (str (name k) "=\"" (escape-html v) "\"")))

(defn- render-attrs
  "Render all attributes from a vdom node's attr map to a string."
  [attrs-map]
  (let [parts (keep (fn [[k v]] (render-attr k v)) attrs-map)]
    (if (seq parts)
      (str " " (str/join " " parts))
      "")))

;; =============================================================================
;; Render to String
;; =============================================================================

(defn render-to-string
  "Render a vdom tree to an HTML string.

  Handles all vnode types:
  - nil -> \"\"
  - TextNode -> escaped text content
  - Fragment -> concatenated children
  - KeyedFragment -> concatenated items
  - Void element (br, img, etc.) -> self-closing tag
  - Regular element -> open tag + children + close tag"
  [vnode]
  (cond
    (nil? vnode)
    ""

    (core/text-node? vnode)
    (escape-html (:content vnode))

    (frag/keyed-fragment? vnode)
    (str/join (map render-to-string (:items vnode)))

    (core/fragment? vnode)
    (str/join (map render-to-string @(:children vnode)))

    (core/element-node? vnode)
    (let [tag (name (:tag vnode))
          attrs (render-attrs @(:attrs vnode))
          void? (void-element? (:tag vnode))]
      (if void?
        (str "<" tag attrs " />")
        (let [children (str/join (map render-to-string @(:children vnode)))]
          (str "<" tag attrs ">" children "</" tag ">"))))

    :else ""))

(defn render-to-string-fragment
  "Render multiple vnodes to a single HTML string.

  Convenience for rendering a vector of vnodes without a wrapper element."
  [vnodes]
  (str/join (map render-to-string vnodes)))
