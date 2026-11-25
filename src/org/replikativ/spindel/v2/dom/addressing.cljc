(ns org.replikativ.spindel.v2.dom.addressing
  "DOM element addresses on engine v2 (phase-d design §2.3-§2.4, A3).

  An element's address hashes its source location, its parent's address
  and its slot in the parent. The parent and slot reach an element in one
  of two ways:

  - Lexically: element macros bind the reserved locals `__dom-parent` and
    `__dom-slot` around each child form. A nested element macro reads them
    from its environment; they survive suspension (continuations close over
    them), and a computation created inside captures them as inputs.
  - Synchronously: a plain function component cannot see its caller's
    locals. The caller runs it under `call-with-context`; its root element
    reads `current`. The context is valid only on the calling thread and
    only until the call returns: it holds a lifetime token, never a run, so
    a binding frame conveyed to a future, a deferred callback or a child
    computation retains only a small dead record."
  (:require [org.replikativ.spindel.engine.hash :as h]
            #?(:clj [replikativ.logging :as log])))

(defn element-address
  "The address of the element at source location `loc` (a map of :file
   :line :column) under `parent` (an address, nil at the root) in `slot`."
  [loc parent slot]
  (keyword (str "el-" (h/content-hash [loc parent slot]))))

(defn keyed-child-address
  "The address of a child keyed by `k` under `parent`: independent of its
   position."
  [parent k]
  (keyword (str "keyed-" (h/content-hash [parent :keyed k]))))

;; ---------------------------------------------------------------------------
;; The synchronous context

(defrecord Ctx [parent slot live])

(def ^:dynamic *context*
  "The synchronous context of a plain component call (a Ctx), or nil."
  nil)

(defn call-with-context
  "Calls `(f)` with the synchronous context `parent`, `slot`: `current`
   returns them on this thread until `f` returns."
  [parent slot f]
  (let [live (volatile! #?(:clj (Thread/currentThread) :cljs true))]
    (try (binding [*context* (->Ctx parent slot live)] (f))
         (finally (vreset! live nil)))))

#?(:clj (def ^:private diagnose?
          "Development builds (assertions on) report a context read outside its call."
          *assert*))

#?(:clj (defonce ^:private diagnosed (atom #{})))

#?(:clj
   (defn- diagnose!
     "Logs ::uncaptured-context once per call site."
     [site]
     (when (and diagnose? (not (contains? @diagnosed site)))
       (swap! diagnosed conj site)
       (log/warn ::uncaptured-context
                 {:site site
                  :note "a context read outside its component call: create the computation with el/component"}))))

(defn current
  "[parent slot] of the synchronous context, or [nil nil] at the root or
   when the context's call has returned or runs on another thread. `site`
   names the reading element for the JVM diagnostic."
  ([] (current nil))
  ([site]
   (let [c *context*]
     (if (nil? c)
       [nil nil]
       (let [o @(:live c)]
         (if (and (some? o) #?(:clj (identical? o (Thread/currentThread)) :cljs true))
           [(:parent c) (:slot c)]
           (do #?(:clj (diagnose! site))
               [nil nil])))))))

#?(:clj
   (defn lexical-context?
     "Macro time: whether the reserved locals are bound in `env`."
     [env]
     (if (:js-globals env)
       (contains? (:locals env) '__dom-parent)
       (contains? env '__dom-parent))))
