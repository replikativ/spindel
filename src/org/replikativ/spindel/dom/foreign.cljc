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
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.addressing :as addr]
            [org.replikativ.spindel.engine.core :as ec]
            [replikativ.logging :as log]))

;; =============================================================================
;; Foreign Node Marker
;; =============================================================================

(defn- mark-foreign!
  "Mark an element address as containing a foreign node.
  This tells the discharge system to skip children.
  Only works when execution context is bound."
  [addr]
  (when ec/*execution-context*
    (ec/swap-state! [:dom/foreign addr] (constantly true))))

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
                     (log/debug ::foreign-node-mount {:addr my-addr :tag tag})
                     (when on-mount
                       (try
                         (on-mount el)
                         (catch #?(:clj Exception :cljs :default) e
                           (log/error ::foreign-node-mount-error {:addr my-addr :error (str e)})))))
                   ;; Unmount
                   (do
                     (log/debug ::foreign-node-unmount {:addr my-addr :tag tag})
                     (when on-unmount
                       (try
                         (on-unmount nil)
                         (catch #?(:clj Exception :cljs :default) e
                           (log/error ::foreign-node-unmount-error {:addr my-addr :error (str e)})))))))

        ;; Merge ref into attrs
        attrs-with-ref (assoc attrs :ref ref-fn)]

    ;; ADDRESSED, not simple-element.
    ;;
    ;; `simple-element` builds a vnode with no `:addr`, so the reconciler has no
    ;; cache to diff its attrs against and emits no attr deltas — the container's
    ;; attributes were therefore FROZEN AT MOUNT. You could not toggle a foreign
    ;; node's :class or :style, ever. That is not a corner: hiding a foreign host
    ;; (a live call, a video, an editor) instead of unmounting it is precisely how
    ;; you keep its state alive, and it is done with a class.
    ;;
    ;; `build-element` reconciles attrs against the address cache, so :class and
    ;; :style now update like any other element. Children stay EMPTY — that part
    ;; was always right: the whole point is that spindel does not own them.
    ;;
    ;; This REQUIRES an execution context, and that is not a limitation — it is
    ;; what a foreign node IS. The caches live in the context, and without one
    ;; there is no reconciliation, no attr deltas, and no lifecycle. Callers that
    ;; have no context do not want a degraded foreign node; they want an error.
    (el/build-element tag my-addr attrs-with-ref [])))

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
       ;; NO context fallback.
       ;;
       ;; This used to degrade to a bare element with the :on-mount/:on-unmount
       ;; callbacks silently DROPPED — which is not a degraded foreign node, it is
       ;; a lie. The lifecycle is the entire point: without it your TipTap,
       ;; CodeMirror or Jitsi call is never constructed, and nothing says so. A
       ;; div that quietly does nothing is the worst possible failure mode.
       ;;
       ;; Nothing legitimate needs that branch: spins always bind a context, and
       ;; SSR never renders foreign nodes (it cannot — there is no DOM to hand the
       ;; library). So an absent context is a BUG at the call site, and it now
       ;; announces itself instead of hiding.
       `(foreign-node* ~source-loc ~opts))))
