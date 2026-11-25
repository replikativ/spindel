(ns org.replikativ.spindel.v2.dom.elements
  "HTML element macros on engine v2 (phase-d design §2.3-§2.6, A3).

  An element macro starts from the current DOM context: the reserved
  locals `__dom-parent`/`__dom-slot` when its environment has them,
  otherwise the synchronous context of a plain component call
  (`addressing/current`, [nil nil] at the root). It binds the locals
  around each child form, so nested elements, computations created inline
  and continuations after an `await` see their parent and slot lexically:

    (el/li attrs c0 c1)
    => (let [p s <context>
             a attrs
             my (addressing/element-address '<loc> p s)
             eff (if-let [k (:key a)] (addressing/keyed-child-address my k) my)
             c0 (let [__dom-parent eff __dom-slot 0] <c0, treated>)
             c1 (let [__dom-parent eff __dom-slot 1] <c1, treated>)]
         (build-element :li my a [c0 c1]))

  A plain function component cannot see the locals; a child form that may
  call one is treated:
  - an effect-free child that contains a call whose head is a local or a
    function var outside clojure.core/cljs.core runs under
    `call-with-context`;
  - an effectful child: a call with effectful arguments is hoisted (the
    arguments bound in order, then the call under the context); in a
    `let`/`let*` each initializer and the last body form, in a `do` the
    last form, in an `if`/`when`/`when-not` the branches are treated by
    these same rules; DOM macros inside see the locals.

  Unsupported positions: a plain component call inside an effectful `loop`,
  `case`, `cond`, `condp`, `try`, threading macro, `doseq`/`for` or any
  other macro; a plain component called from a helper function that is
  itself called after a suspension; a component result computed after a
  suspension and passed through a local defined outside the child form.
  Use `in-context` there. A recognizable unsupported form prints the
  compile-time warning ::unaddressed-call with its location.

  Computations: an inline `spin` in a child captures the locals; a
  computation made by a plain component is created with `component`."
  (:require [clojure.string :as str]
            [org.replikativ.spindel.dom.core :as core]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.dom.addressing :as addr]
            #?(:clj [is.simm.partial-cps.ioc :as ioc]))
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.dom.elements])))

;; ---------------------------------------------------------------------------
;; Building a vnode (plain values)

(defn- normalize-child
  "A child as a vnode, a KeyedFragment, or nil."
  [child]
  (cond
    (nil? child) nil
    (core/vnode? child) child
    (frag/keyed-fragment? child) child
    (string? child) (core/make-text-vnode child)
    (number? child) (core/make-text-vnode (str child))
    :else (core/make-text-vnode (str child))))

(defn- flatten-and-normalize
  "Flattens sequences (not KeyedFragments) and normalizes every child; a
   nil child keeps its place."
  [children]
  (->> children
       (mapcat (fn [c]
                 (cond
                   (nil? c) [nil]
                   (frag/keyed-fragment? c) [c]
                   (and (sequential? c) (not (core/vnode? c))) c
                   :else [c])))
       (mapv normalize-child)))

(defn make-slot
  "A slot entry {:type :nil|:single|:keyed :value child} for a child."
  [child]
  {:type (cond
           (nil? child) :nil
           (frag/keyed-fragment? child) :keyed
           (core/vnode? child) :single
           (vector? child) :keyed
           :else :single)
   :value child})

(defn- flatten-slot [slot]
  (case (:type slot)
    :nil []
    :single [(:value slot)]
    :keyed (if (frag/keyed-fragment? (:value slot))
             (:items (:value slot))
             (:value slot))
    []))

(defn flatten-slots
  "The children vector of a vector of slots."
  [slots]
  (into [] (mapcat flatten-slot) slots))

(defn build-element
  "A vnode of plain values from evaluated children. `my-addr` is the
   element's structural address; with a :key in `attrs` the vnode's :addr
   is keyed under it. The slots keep a nil child's place, so a later
   sibling's position does not shift."
  [tag my-addr attrs children]
  (let [k (:key attrs)
        ref-fn (:ref attrs)
        slots (mapv make-slot (flatten-and-normalize children))]
    (cond-> {:tag tag
             :addr (if k (addr/keyed-child-address my-addr k) my-addr)
             :attrs (dissoc attrs :key :ref)
             :slots slots
             :children (flatten-slots slots)}
      k (assoc :key k)
      ref-fn (assoc :ref ref-fn))))

(defn fragment
  "Several children without a wrapper element."
  [& children]
  {:tag :fragment :children (flatten-and-normalize children)})

(defn text
  "A text node."
  [content]
  (core/make-text-vnode content))

;; ---------------------------------------------------------------------------
;; Macro time: treating child forms (§2.4-§2.5)

#?(:clj
   (do
     (def ^:private reserved '[__dom-parent __dom-slot])

     ;; locations already warned about: an element form is expanded several
     ;; times (partial-cps, the free-variable analysis, the compiler)
     (defonce ^:private warned (atom #{}))

     (defn- local? [env sym]
       (if (:js-globals env) (contains? (:locals env) sym) (contains? env sym)))

     (defn- macro-meta
       "The var metadata of macro `h` in `env`, or nil."
       [env h]
       (when (and (symbol? h) (not (local? env h)))
         (if (:js-globals env)
           (let [m (ioc/resolve-macro-var-cljs env h)] (when (:macro m) m))
           (let [v (try (resolve env h) (catch Exception _ nil))]
             (when (and (var? v) (:macro (meta v))) (meta v))))))

     (defn- dom-macro? [env h] (boolean (::dom-macro (macro-meta env h))))

     (defn- special? [env h]
       (or (special-symbol? h)
           (and (:js-globals env) (contains? @(requiring-resolve 'cljs.analyzer/specials) h))))

     (defn- head-name [env h] (try (ioc/var-name env h) (catch Exception _ nil)))

     (defn- interop? [h]
       (let [n (name h)] (or (str/starts-with? n ".") (str/ends-with? n "."))))

     (defn- component-head?
       "Whether a call of `h` may be a plain component: `h` is a local, or a
        function var outside clojure.core/cljs.core. Macros, effects,
        special forms and interop are not."
       [env h]
       (cond
         (not (symbol? h)) false
         (local? env h) true
         (special? env h) false
         (macro-meta env h) false
         (interop? h) false
         (v2/effectful? env (list h)) false
         :else (let [q (head-name env h)]
                 (boolean (and q (namespace q)
                               (not (#{"clojure.core" "cljs.core" "js"} (namespace q))))))))

     (defn- component-call-in?
       "Whether `form` calls a possible component in its own scope, outside
        DOM macros (they place their own children)."
       [env form]
       (boolean (v2/scope-some env form
                               (fn [env x]
                                 (let [h (first x)]
                                   (cond (dom-macro? env h) ::v2/skip
                                         (component-head? env h) true))))))

     (defn- wrap [form]
       `(addr/call-with-context ~'__dom-parent ~'__dom-slot (fn [] ~form)))

     (defn- warn-if-unaddressed!
       "Prints ::unaddressed-call for an effectful `form` the rules do not
        handle when it calls a possible component."
       [env loc form]
       (when (component-call-in? env form)
         (let [at (merge loc (select-keys (meta form) [:line :column]))]
           (when-not (contains? @warned at)
             (swap! warned conj at)
             (binding [*out* *err*]
               (println "WARNING:" ::unaddressed-call (pr-str at)
                        "- a plain component called here after a suspension gets no DOM context;"
                        "wrap the call in el/in-context"))))))

     (declare treat)

     (defn- treat-let [env loc [h bvec & body :as form]]
       (let [[bvec' env'] (loop [ps (partition 2 bvec) out [] env env]
                            (if-let [[b init] (first ps)]
                              (recur (rest ps) (conj out b (treat env loc init))
                                     (ioc/bind-locals env (ioc/binding-symbols b)))
                              [out env]))]
         (with-meta (if (seq body)
                      `(~h ~bvec' ~@(butlast body) ~(treat env' loc (last body)))
                      `(~h ~bvec'))
           (meta form))))

     (defn- treat-last [env loc form n]
       ;; the forms of `form` after the first `n` are a body: treat its last
       (let [[head body] (split-at n form)]
         (with-meta (if (seq body)
                      `(~@head ~@(butlast body) ~(treat env loc (last body)))
                      form)
           (meta form))))

     (defn- treat-if [env loc [h test then & more :as form]]
       (with-meta `(~h ~test ~(treat env loc then) ~@(map #(treat env loc %) more)) (meta form)))

     (defn- hoist
       "A call with effectful arguments: the arguments bound in order (each
        treated), then the call, under the context if it may be a component."
       [env loc [h & args :as form]]
       (if-not (or (component-head? env h) (some #(component-call-in? env %) args))
         form
         (let [ts (mapv (fn [_] (gensym "arg")) args)
               call (with-meta (list* h ts) (meta form))]
           `(let [~@(interleave ts (map #(treat env loc %) args))]
              ~(if (component-head? env h) (wrap call) call)))))

     (defn- treat
       "A child form (or a part of one, §2.5) in `env`, where the reserved
        locals are bound."
       [env loc form]
       (cond
         (not (v2/effectful? env form))
         (if (component-call-in? env form) (wrap form) form)

         (not (and (seq? form) (symbol? (first form))))
         (do (warn-if-unaddressed! env loc form) form)

         :else
         (let [h (first form)]
           (cond
             (dom-macro? env h) form
             (local? env h) (hoist env loc form)
             (special? env h) (case h
                                let* (treat-let env loc form)
                                do (treat-last env loc form 1)
                                if (treat-if env loc form)
                                (do (warn-if-unaddressed! env loc form) form))
             :else
             (let [q (head-name env h)]
               (cond
                 (#{'clojure.core/let 'cljs.core/let} q) (treat-let env loc form)
                 (#{'clojure.core/when 'cljs.core/when 'clojure.core/when-not 'cljs.core/when-not} q)
                 (treat-last env loc form 2)
                 (or (macro-meta env h) (interop? h))
                 (do (warn-if-unaddressed! env loc form) form)
                 :else (hoist env loc form)))))))

     (defn- context-bindings
       "Bindings of `p` and `s` to the current DOM context in `env`."
       [env loc p s]
       (if (addr/lexical-context? env)
         [p '__dom-parent s '__dom-slot]
         (let [c (gensym "context")]
           [c `(addr/current '~loc) p `(nth ~c 0) s `(nth ~c 1)])))

     (defn- source-loc
       "The location of `form`. The file is the source's classpath path on
        both platforms (D2): `*file*` on the JVM; ClojureScript compilers do
        not bind `*file*` (it is \"NO_SOURCE_PATH\" under shadow-cljs) but
        `cljs.analyzer/*cljs-file*`."
       [env form]
       {:file (if (:js-globals env)
                (some-> (resolve 'cljs.analyzer/*cljs-file*) deref str)
                *file*)
        :line (:line (meta form))
        :column (:column (meta form))})

     (defn- element-form
       "The expansion of an element with tag form `tag` and arguments `args`."
       [tag args form env]
       (let [loc (source-loc env form)
             [attrs children] (if (and (seq args) (map? (first args)) (not (:tag (first args))))
                                [(first args) (rest args)]
                                [nil args])
             p (gensym "parent") s (gensym "slot") a (gensym "attrs")
             my (gensym "addr") eff (gensym "eff")
             cenv (ioc/bind-locals env (into reserved [p s a my eff]))
             cs (mapv (fn [_] (gensym "child")) children)]
         `(let [~@(context-bindings env loc p s)
                ~a ~(or attrs {})
                ~my (addr/element-address '~loc ~p ~s)
                ~eff (if-let [k# (:key ~a)] (addr/keyed-child-address ~my k#) ~my)
                ~@(mapcat (fn [i c child]
                            [c `(let [~'__dom-parent ~eff ~'__dom-slot ~i] ~(treat cenv loc child))])
                          (range) cs children)]
            (build-element ~tag ~my ~a [~@cs]))))

     (def ^:private element-doc
       "An HTML element: (tag attrs? & children). See the namespace doc for
        how children are addressed and the unsupported positions.")

     (defmacro ^:private defelements [& specs]
       `(do ~@(for [[nm tag] (partition 2 specs)]
                `(defmacro ~(with-meta nm {::dom-macro true ::v2/scope ::v2/transparent
                                           :doc element-doc :arglists ''([& args])})
                   [& args#]
                   (element-form ~tag args# ~'&form ~'&env)))))))

;; ---------------------------------------------------------------------------
;; Elements

#?(:clj
   (defelements
     div :div, span :span, p :p,
     h1 :h1, h2 :h2, h3 :h3, h4 :h4, h5 :h5, h6 :h6,
     header :header, footer :footer, main :main, section :section, article :article,
     aside :aside, nav :nav, pre :pre, code :code, blockquote :blockquote,
     details :details, summary :summary, hr :hr, br :br,
     ul :ul, ol :ol, li :li, dl :dl, dt :dt, dd :dd,
     table :table, thead :thead, tbody :tbody, tfoot :tfoot, tr :tr, th :th, td :td,
     form :form, input :input, textarea :textarea, button :button, select :select,
     option :option, label :label, fieldset :fieldset, legend :legend,
     a :a, strong :strong, em :em, b :b, i :i, u :u, small :small, sub :sub, sup :sup,
     img :img, video :video, audio :audio, source :source, canvas :canvas, svg :svg,
     html :html, head :head, body :body, title :title, meta-tag :meta, link :link,
     script :script, style :style))

#?(:clj
   (defmacro ^{::dom-macro true ::v2/scope ::v2/transparent} element
     "An element with a dynamic tag: (element tag attrs? & children)."
     [tag & args]
     (element-form tag args &form &env)))

#?(:clj
   (defmacro ^{::dom-macro true ::v2/scope ::v2/transparent} in-context
     "The explicit boundary: runs the effect-free `body` under the current
      DOM context (the reserved locals, or the synchronous context), so a
      plain component called in it is placed there. Usable after a
      suspension: (case (await mode) :a (el/in-context (card-a x)) ...)."
     [& body]
     (if (addr/lexical-context? &env)
       `(addr/call-with-context ~'__dom-parent ~'__dom-slot (fn [] ~@body))
       (let [c (gensym "context")]
         `(let [~c (addr/current '~(source-loc &env &form))]
            (addr/call-with-context (nth ~c 0) (nth ~c 1) (fn [] ~@body)))))))

#?(:clj
   (defmacro ^{::dom-macro true ::v2/scope ::v2/opaque} component
     "A computation made by a plain component: (component body...) is a
      `spin` whose body's elements are placed at the component's DOM
      context, captured as an input (moved, it reruns). The spin keeps this
      form's source location as its creation site."
     [& body]
     (let [spin-form (with-meta `(v2/spin ~@body) (meta &form))]
       (if (addr/lexical-context? &env)
         spin-form
         `(let [[~'__dom-parent ~'__dom-slot] (addr/current '~(source-loc &env &form))]
            ~spin-form)))))
