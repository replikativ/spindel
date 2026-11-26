(ns org.replikativ.spindel.v2.dom.foreign
  "Foreign nodes on engine v2: a container element whose children an
  external library manages (TipTap, CodeMirror, a video player), not the
  vdom.

    (foreign-node {:tag :pre :class \"editor\"
                   :on-mount (fn [el] (reset! editor (Editor. #js {:element el})))
                   :on-unmount (fn [_] (.destroy @editor))})

  The options map onto the lifetime hook `:ref` (phase-d addendum §3.8.2):
  `:on-mount` runs once the container is created and attached, after the
  commit's DOM writes; `:on-unmount` is its cleanup, called with nil before
  the container is removed. An attr change (a class, a style) reconciles
  the container in place, without a remount; its children are never
  touched. A throwing `:on-mount` is reported and registers no cleanup, so
  `:on-unmount` does not follow it. Every other option is an attr of the
  container; `:tag` defaults to :div."
  (:require [org.replikativ.spindel.v2.dom.elements :as el])
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.dom.foreign :refer [foreign-node]])))

(defn ^:no-doc foreign-ref
  "The container's :ref: on-mount, returning on-unmount as the cleanup."
  [{:keys [on-mount on-unmount]}]
  (fn [el]
    (when on-mount (on-mount el))
    (fn [] (when on-unmount (on-unmount nil)))))

(defn ^:no-doc with-attrs
  "The container vnode with the options' attrs."
  [vnode opts]
  (update vnode :attrs merge (dissoc opts :tag :key :on-mount :on-unmount)))

#?(:clj
   (defmacro foreign-node
     "A foreign-node container, addressed like any element at this form's
      location. `opts`: :tag (default :div), :on-mount (fn [el]),
      :on-unmount (fn [_]), :key, and the container's attrs. Children are
      the library's; pass none."
     [opts]
     (let [o (gensym "opts")]
       `(let [~o ~opts]
          (with-attrs ~(with-meta `(el/element (or (:tag ~o) :div) {:key (:key ~o) :ref (foreign-ref ~o)})
                         (meta &form))
            ~o)))))
