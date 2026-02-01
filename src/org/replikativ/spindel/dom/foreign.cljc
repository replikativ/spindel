(ns org.replikativ.spindel.dom.foreign
  "Foreign node support for integrating external DOM libraries.

  A foreign node is a DOM container whose children are managed by an external
  library (TipTap, CodeMirror, etc.) rather than by spindel's vdom system.

  **How it works:**

  1. `foreign-node` creates a container element (div by default)
  2. The container uses :ref callback to get lifecycle notifications
  3. User provides :on-mount and :on-unmount callbacks
  4. On mount: callback receives the DOM element, user initializes their library
  5. On unmount: callback receives nil, user cleans up their library
  6. Spindel never touches the container's children - they're foreign territory

  **Usage:**

    (require '[org.replikativ.spindel.dom.foreign :as foreign])

    ;; Simple usage with TipTap
    (foreign/foreign-node
      {:on-mount (fn [el]
                   (let [editor (Editor. #js {:element el
                                              :content \"Hello\"})]
                     (reset! editor-atom editor)))
       :on-unmount (fn [_]
                     (when-let [editor @editor-atom]
                       (.destroy editor)
                       (reset! editor-atom nil)))})

    ;; With custom tag and attrs
    (foreign/foreign-node
      {:tag :pre
       :class \"code-editor\"
       :on-mount init-codemirror
       :on-unmount cleanup-codemirror})

  **Integration with signals:**

  The mount callback can set up event listeners that update spindel signals:

    (foreign/foreign-node
      {:on-mount (fn [el]
                   (let [editor (Editor. #js {:element el})]
                     ;; Update signal on content change
                     (.on editor \"update\" #(reset! content-signal (.getHTML editor)))
                     (reset! editor-atom editor)))
       :on-unmount (fn [_] ...)})

  **Important notes:**

  - The container element is managed by spindel (attributes, position in tree)
  - The container's children are NOT managed by spindel
  - Never pass children to foreign-node - they will be ignored
  - The mount/unmount callbacks are synchronous
  - Multiple mounts/unmounts may occur if the element is conditionally rendered"
  (:require [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.core :as core]
            [org.replikativ.spindel.dom.addressing :as addr]
            [org.replikativ.spindel.dom.cache :as cache]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.log :as log]))

;; =============================================================================
;; Foreign Node Marker
;; =============================================================================

(defn- mark-foreign!
  "Mark an element address as containing a foreign node.
  This tells the discharge system to skip children.
  Only works when execution context is bound."
  [addr]
  (when rtc/*execution-context*
    (rtc/swap-state! [:dom/foreign addr] (constantly true))))

(defn- foreign?
  "Check if an address contains a foreign node."
  [addr]
  (when rtc/*execution-context*
    (rtc/get-state [:dom/foreign addr])))

;; =============================================================================
;; Foreign Node Implementation
;; =============================================================================

(defn foreign-node*
  "Internal implementation for foreign-node.

  Args:
    source-loc - Source location map for addressing
    opts - Options map with:
      :tag - HTML tag (default :div)
      :on-mount - (fn [el]) called when element is mounted
      :on-unmount - (fn [el]) called when element is unmounted (el is nil)
      + any standard HTML attributes (:class, :style, etc.)"
  [source-loc opts]
  (let [{:keys [tag on-mount on-unmount]
         :or {tag :div}} opts

        ;; Extract standard attrs (everything except our special keys)
        attrs (dissoc opts :tag :on-mount :on-unmount)

        ;; Compute this element's address
        my-addr (addr/current-element-address source-loc)

        ;; Mark this address as foreign
        _ (mark-foreign! my-addr)

        ;; Create ref callback that wraps mount/unmount
        ref-fn (fn [el]
                 (if el
                   ;; Mount
                   (do
                     (log/debug! {:event ::foreign-node-mount
                                  :data {:addr my-addr :tag tag}})
                     (when on-mount
                       (try
                         (on-mount el)
                         (catch #?(:clj Exception :cljs :default) e
                           (log/error! {:event ::foreign-node-mount-error
                                        :data {:addr my-addr :error (str e)}})))))
                   ;; Unmount
                   (do
                     (log/debug! {:event ::foreign-node-unmount
                                  :data {:addr my-addr :tag tag}})
                     (when on-unmount
                       (try
                         (on-unmount nil)
                         (catch #?(:clj Exception :cljs :default) e
                           (log/error! {:event ::foreign-node-unmount-error
                                        :data {:addr my-addr :error (str e)}})))))))

        ;; Merge ref into attrs
        attrs-with-ref (assoc attrs :ref ref-fn)]

    ;; Create the container element with no children
    ;; We use simple-element since we don't need caching for children
    ;; but we want the element to participate in parent's slot reconciliation
    (el/simple-element tag attrs-with-ref [])))

;; =============================================================================
;; Macro: foreign-node
;; =============================================================================

#?(:clj
   (defmacro foreign-node
     "Create a foreign node container.

     A foreign node is a DOM element whose children are managed by an external
     library rather than by spindel. Use this to integrate TipTap, CodeMirror,
     or any other library that needs to control its own DOM children.

     Args (as opts map):
       :tag - HTML tag for container (default :div)
       :on-mount - (fn [el]) called when element is mounted to DOM
       :on-unmount - (fn [_]) called when element is unmounted
       + any standard HTML attributes

     The mount callback receives the actual DOM element. Use it to initialize
     your external library. The unmount callback is for cleanup.

     Example:
       (foreign-node
         {:class \"editor-container\"
          :on-mount (fn [el]
                      (let [editor (TipTap/Editor. #js {:element el})]
                        (reset! editor-ref editor)))
          :on-unmount (fn [_]
                        (when-let [ed @editor-ref]
                          (.destroy ed)))})"
     [opts]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(if rtc/*execution-context*
          (foreign-node* ~source-loc ~opts)
          ;; Without context: create simple element (no lifecycle callbacks)
          (el/simple-element (:tag ~opts :div)
                             (dissoc ~opts :tag :on-mount :on-unmount)
                             [])))))
