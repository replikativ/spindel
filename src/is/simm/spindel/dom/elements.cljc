(ns is.simm.spindel.dom.elements
  "HTML element macros for delta-direct DOM rendering.

  All elements (div, span, ul, etc.) are MACROS that:
  1. Capture source location at compile time
  2. Wrap children in thunks for deferred evaluation
  3. Call implementation function with source-loc and thunks

  The implementation functions:
  1. Compute tree address from source-loc + parent-addr + slot
  2. Evaluate children with proper context bindings
  3. Compare with cached slots, produce deltas
  4. Return vnode with deltas attached

  Usage:
    (el/div {:class \"container\"}
      (el/span \"hello\")
      (when show-modal
        (el/div {:class \"modal\"} \"content\")))

  Each element gets unique address based on position in tree.
  Conditionals work naturally - nil slots produce add/remove deltas.

  BREAKING CHANGE from v1:
  - Elements are macros, not functions
  - Can't pass directly to map: use (fn [x] (el/div x)) instead
  - Requires execution context for caching"
  (:require [is.simm.spindel.dom.core :as core]
            [is.simm.spindel.dom.addressing :as addr]
            [is.simm.spindel.dom.cache :as cache]
            [is.simm.spindel.dom.fragment :as frag]
            [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.log :as log]))

;; =============================================================================
;; Argument Parsing (same as before)
;; =============================================================================

(defn- attrs-map?
  "Check if x looks like an attrs map (not a vnode or sequence)."
  [x]
  (and (map? x)
       (not (core/vnode? x))
       (not (frag/keyed-fragment? x))))

(defn parse-element-args
  "Parse element arguments into [attrs children].

  Handles flexible argument patterns:
    (div {:class \"x\"} child1 child2)
    (div child1 child2)  ; no attrs
    (div {:class \"x\"})  ; no children
    (div)"
  [args]
  (if (attrs-map? (first args))
    [(first args) (rest args)]
    [{} args]))

;; =============================================================================
;; Child Normalization
;; =============================================================================

(defn- normalize-child
  "Normalize a child to a vnode, KeyedFragment, or nil."
  [child]
  (cond
    (nil? child) nil
    (core/vnode? child) child
    (frag/keyed-fragment? child) child
    (string? child) (core/make-text-vnode child)
    (number? child) (core/make-text-vnode (str child))
    ;; Flatten sequences (but not KeyedFragment)
    (sequential? child) nil  ; Will be handled by flatten
    :else (core/make-text-vnode (str child))))

(defn- flatten-and-normalize
  "Flatten sequences and normalize all children."
  [children]
  (->> children
       (mapcat (fn [c]
                 (cond
                   (nil? c) [nil]  ; Keep nil for slot tracking
                   (frag/keyed-fragment? c) [c]
                   (and (sequential? c) (not (core/vnode? c))) c
                   :else [c])))
       (mapv normalize-child)))

;; =============================================================================
;; Element Implementation (runtime)
;; =============================================================================

(defn element*
  "Create a vnode with delta tracking.

  This is the runtime implementation called by element macros.

  Args:
    tag - Keyword for HTML tag
    source-loc - Map with :file :line :column
    attrs - Attribute map
    child-thunks - Vector of zero-arg functions returning children

  Returns: VNode with :deltas if any changes detected"
  [tag source-loc attrs child-thunks]
  (let [;; Compute this element's address
        my-addr (addr/current-element-address source-loc)

        ;; Get previous caches
        prev-slot-cache (cache/get-slot-cache my-addr)
        prev-attrs (cache/get-attr-cache my-addr)

        ;; Clean attrs (remove :key and :ref which are handled separately)
        attrs-clean (dissoc attrs :key :ref)

        ;; Reconcile attrs with cache
        attr-deltas (cache/reconcile-attrs prev-attrs attrs-clean)

        ;; Update attr cache
        _ (cache/set-attr-cache! my-addr attrs-clean)

        ;; Evaluate each child thunk with proper slot context
        new-children
        (addr/with-parent-addr my-addr
          (fn []
            (vec (map-indexed
                   (fn [idx thunk]
                     (addr/with-slot idx
                       (fn []
                         (thunk))))
                   child-thunks))))

        ;; Normalize children (handle text, nil, sequences)
        normalized-children (flatten-and-normalize new-children)

        ;; Reconcile children with cache
        {:keys [slots deltas]} (cache/reconcile-children prev-slot-cache normalized-children)

        ;; Update slot cache
        _ (cache/set-slot-cache! my-addr slots)

        ;; Flatten slots to final children vector
        final-children (cache/flatten-slots slots)

        ;; Adjust delta paths to absolute indices
        adjusted-deltas (when (seq deltas)
                          (cache/adjust-delta-paths slots deltas))

        ;; Build vnode with attrs that carry deltas
        ;; Use deltaable-map-with-deltas so discharge can see attr changes
        key-val (:key attrs)
        ref-fn (:ref attrs)
        attrs-with-deltas (is.simm.spindel.incremental.deltaable/deltaable-map-with-deltas
                            attrs-clean attr-deltas)
        vnode (cond-> {:tag tag
                       :attrs attrs-with-deltas
                       :children (is.simm.spindel.incremental.deltaable/deltaable-vector
                                   (vec final-children))}
                key-val (assoc :key key-val)
                ref-fn (assoc :ref ref-fn))]

    ;; Attach child deltas if any
    (if (seq adjusted-deltas)
      (assoc vnode :deltas adjusted-deltas)
      vnode)))

;; =============================================================================
;; Simple Element (no caching, for use outside context)
;; =============================================================================

(defn simple-element
  "Create a simple vnode without delta tracking.

  Use this when:
  - No execution context is available
  - Building static vdom (tests, SSR)
  - Performance: skip caching overhead for known-static content"
  [tag attrs children]
  (let [normalized (flatten-and-normalize children)]
    (core/make-vnode tag attrs normalized)))

;; =============================================================================
;; Element Macro Generator
;; =============================================================================

#?(:clj
   (defn- make-element-macro
     "Generate the macro body for an element.

     The macro:
     1. Captures source location
     2. Parses attrs vs children
     3. Wraps each child in a thunk
     4. Calls element* at runtime"
     [tag args form]
     (let [source-loc {:file *file*
                       :line (:line (meta form))
                       :column (:column (meta form))}
           ;; Parse at macro time if possible
           [attrs children] (if (and (seq args)
                                     (map? (first args))
                                     (not (:tag (first args))))
                              [(first args) (rest args)]
                              [nil args])
           attrs-form (or attrs {})
           ;; Wrap each child expression in a thunk
           child-thunks (mapv (fn [child-expr]
                                `(fn [] ~child-expr))
                              children)]
       `(if rtc/*execution-context*
          ;; With context: use caching element
          (element* ~tag ~source-loc ~attrs-form ~child-thunks)
          ;; Without context: simple element (no caching)
          (simple-element ~tag ~attrs-form [~@children])))))

;; =============================================================================
;; Block Elements
;; =============================================================================

#?(:clj
   (defmacro div [& args]
     (make-element-macro :div args &form)))

#?(:clj
   (defmacro span [& args]
     (make-element-macro :span args &form)))

#?(:clj
   (defmacro p [& args]
     (make-element-macro :p args &form)))

#?(:clj (defmacro h1 [& args] (make-element-macro :h1 args &form)))
#?(:clj (defmacro h2 [& args] (make-element-macro :h2 args &form)))
#?(:clj (defmacro h3 [& args] (make-element-macro :h3 args &form)))
#?(:clj (defmacro h4 [& args] (make-element-macro :h4 args &form)))
#?(:clj (defmacro h5 [& args] (make-element-macro :h5 args &form)))
#?(:clj (defmacro h6 [& args] (make-element-macro :h6 args &form)))

#?(:clj (defmacro header [& args] (make-element-macro :header args &form)))
#?(:clj (defmacro footer [& args] (make-element-macro :footer args &form)))
#?(:clj (defmacro main [& args] (make-element-macro :main args &form)))
#?(:clj (defmacro section [& args] (make-element-macro :section args &form)))
#?(:clj (defmacro article [& args] (make-element-macro :article args &form)))
#?(:clj (defmacro aside [& args] (make-element-macro :aside args &form)))
#?(:clj (defmacro nav [& args] (make-element-macro :nav args &form)))

#?(:clj (defmacro pre [& args] (make-element-macro :pre args &form)))
#?(:clj (defmacro code [& args] (make-element-macro :code args &form)))
#?(:clj (defmacro blockquote [& args] (make-element-macro :blockquote args &form)))

#?(:clj (defmacro hr [& args] (make-element-macro :hr args &form)))
#?(:clj (defmacro br [& args] (make-element-macro :br args &form)))

;; =============================================================================
;; Lists
;; =============================================================================

#?(:clj (defmacro ul [& args] (make-element-macro :ul args &form)))
#?(:clj (defmacro ol [& args] (make-element-macro :ol args &form)))
#?(:clj (defmacro li [& args] (make-element-macro :li args &form)))
#?(:clj (defmacro dl [& args] (make-element-macro :dl args &form)))
#?(:clj (defmacro dt [& args] (make-element-macro :dt args &form)))
#?(:clj (defmacro dd [& args] (make-element-macro :dd args &form)))

;; =============================================================================
;; Tables
;; =============================================================================

#?(:clj (defmacro table [& args] (make-element-macro :table args &form)))
#?(:clj (defmacro thead [& args] (make-element-macro :thead args &form)))
#?(:clj (defmacro tbody [& args] (make-element-macro :tbody args &form)))
#?(:clj (defmacro tfoot [& args] (make-element-macro :tfoot args &form)))
#?(:clj (defmacro tr [& args] (make-element-macro :tr args &form)))
#?(:clj (defmacro th [& args] (make-element-macro :th args &form)))
#?(:clj (defmacro td [& args] (make-element-macro :td args &form)))

;; =============================================================================
;; Forms
;; =============================================================================

#?(:clj (defmacro form [& args] (make-element-macro :form args &form)))
#?(:clj (defmacro input [& args] (make-element-macro :input args &form)))
#?(:clj (defmacro textarea [& args] (make-element-macro :textarea args &form)))
#?(:clj (defmacro button [& args] (make-element-macro :button args &form)))
#?(:clj (defmacro select [& args] (make-element-macro :select args &form)))
#?(:clj (defmacro option [& args] (make-element-macro :option args &form)))
#?(:clj (defmacro label [& args] (make-element-macro :label args &form)))
#?(:clj (defmacro fieldset [& args] (make-element-macro :fieldset args &form)))
#?(:clj (defmacro legend [& args] (make-element-macro :legend args &form)))

;; =============================================================================
;; Inline Elements
;; =============================================================================

#?(:clj (defmacro a [& args] (make-element-macro :a args &form)))
#?(:clj (defmacro strong [& args] (make-element-macro :strong args &form)))
#?(:clj (defmacro em [& args] (make-element-macro :em args &form)))
#?(:clj (defmacro b [& args] (make-element-macro :b args &form)))
#?(:clj (defmacro i [& args] (make-element-macro :i args &form)))
#?(:clj (defmacro u [& args] (make-element-macro :u args &form)))
#?(:clj (defmacro small [& args] (make-element-macro :small args &form)))
#?(:clj (defmacro sub [& args] (make-element-macro :sub args &form)))
#?(:clj (defmacro sup [& args] (make-element-macro :sup args &form)))

;; =============================================================================
;; Media
;; =============================================================================

#?(:clj (defmacro img [& args] (make-element-macro :img args &form)))
#?(:clj (defmacro video [& args] (make-element-macro :video args &form)))
#?(:clj (defmacro audio [& args] (make-element-macro :audio args &form)))
#?(:clj (defmacro source [& args] (make-element-macro :source args &form)))
#?(:clj (defmacro canvas [& args] (make-element-macro :canvas args &form)))
#?(:clj (defmacro svg [& args] (make-element-macro :svg args &form)))

;; =============================================================================
;; Document Structure (for SSR)
;; =============================================================================

#?(:clj (defmacro html [& args] (make-element-macro :html args &form)))
#?(:clj (defmacro head [& args] (make-element-macro :head args &form)))
#?(:clj (defmacro body [& args] (make-element-macro :body args &form)))
#?(:clj (defmacro title [& args] (make-element-macro :title args &form)))
#?(:clj (defmacro meta-tag [& args] (make-element-macro :meta args &form)))
#?(:clj (defmacro link [& args] (make-element-macro :link args &form)))
#?(:clj (defmacro script [& args] (make-element-macro :script args &form)))
#?(:clj (defmacro style [& args] (make-element-macro :style args &form)))

;; =============================================================================
;; Special Elements
;; =============================================================================

(defn fragment
  "Create a fragment (multiple children without wrapper element).

  Note: This is a function, not macro, since fragments don't need
  their own address - their children get addresses from the parent."
  [& children]
  (core/make-fragment-vnode (flatten-and-normalize children)))

(defn text
  "Create a text node explicitly."
  [content]
  (core/make-text-vnode content))

;; =============================================================================
;; Generic Element (for dynamic tag names)
;; =============================================================================

#?(:clj
   (defmacro element
     "Create an element with dynamic tag name.

     Usage:
       (element :div {:class \"x\"} child1 child2)
       (element tag-var attrs & children)"
     [tag & args]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}
           [attrs children] (if (and (seq args)
                                     (map? (first args))
                                     (not (:tag (first args))))
                              [(first args) (rest args)]
                              [nil args])
           attrs-form (or attrs {})
           child-thunks (mapv (fn [child-expr]
                                `(fn [] ~child-expr))
                              children)]
       `(if rtc/*execution-context*
          (element* ~tag ~source-loc ~attrs-form ~child-thunks)
          (simple-element ~tag ~attrs-form [~@children])))))
