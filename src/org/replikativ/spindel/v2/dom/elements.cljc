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

  A plain function component cannot see the locals. A child form is
  treated so that every plain component it may call runs under the
  context. A possible component call is a call whose head is a local or a
  function var outside clojure.core/cljs.core (not a macro or an effect),
  or an indirect one: a component var or a function literal that calls one
  passed as an argument, a local passed as the function of a core
  higher-order function (`apply`, `mapv`, `reduce`, ...), a `for`/`doseq`
  that calls one.
  - An effect-free form that may call a component runs under
    `call-with-context`.
  - An effectful form is taken apart in a closed set of shapes, whose
    parts are treated by these same rules: a call (its operands bound in
    evaluation order, var reads included; locals, literals and function
    literals left in place; then the call), `let`/`let*` (destructuring lowered first; every initializer and
    body form), `do`, `if`, `when`/`when-not` (every form). DOM macros see
    the locals; an inline `spin`'s body is treated too.

  Unsupported, with the compile-time warning ::unaddressed-call at the
  form's location:
  - a possible component call in any other effectful form after a
    suspension (`loop`, `case`, `cond`, `condp`, `try`, a threading macro,
    any other macro);
  - a lazy sequence of component calls (`map`, `for`, ...): it is realized
    later, outside the context; use an eager form (`mapv`, `into []`);
  - a computation or task created in a position the rules do not reach
    (or a task anywhere) whose body calls a plain component.
  Recognized and placed: a helper function called directly in a supported
  shape, also after a suspension (it is a possible component call). Not
  recognizable, so not warned: a component called through a function value
  the rules cannot see (a map lookup, a field, a local handed to a function
  other than the core higher-order ones), or by a helper that is itself
  called that way. Use `in-context` there. The lazy warning is conservative: an eager
  consumer around `map` (`(vec (map card xs))`) warns too; prefer `mapv`.

  Computations: an inline `spin` in a child captures the locals; a
  computation made by a plain component is created with `component`."
  (:require [clojure.string :as str]
            [org.replikativ.spindel.dom.core :as core]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.dom.addressing :as addr]
            #?(:clj [org.replikativ.spindel.v2.macro-support :as ms])
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

     (defn- dom-macro? [env h] (boolean (::dom-macro (ms/macro-meta env h))))

     (defn- interop? [h]
       (let [n (name h)] (or (str/starts-with? n ".") (str/ends-with? n "."))))

     (defn- core-name? [q]
       (boolean (and q (#{"clojure.core" "cljs.core"} (namespace q)))))

     (defn- inline-fn?
       "Whether `h` names a ClojureScript core function that also has a
        macro (`some?`, `+`, ...): a call of it is a function call."
       [env h]
       (and (:js-globals env)
            (let [q (ms/head-name env h)]
              (and (core-name? q)
                   (some? (get-in @@(requiring-resolve 'cljs.env/*compiler*)
                                  [:cljs.analyzer/namespaces 'cljs.core :defs (symbol (name q))]))))))

     (defn- component-var?
       "Whether symbol `h` names a function var that may be a plain
        component: outside clojure.core/cljs.core, not a macro, an effect,
        a special form or interop."
       [env h]
       (and (symbol? h)
            (not (ms/local? env h))
            (not (ms/special? env h))
            (not (ms/macro-meta env h))
            (not (interop? h))
            (not (v2/effectful? env (list h)))
            (let [q (ms/head-name env h)]
              (boolean (and q (namespace q) (not (core-name? q)) (not= "js" (namespace q)))))))

     (defn- component-head?
       "Whether a call of `h` may be a plain component: `h` is a local or a
        component var."
       [env h]
       (and (symbol? h) (or (ms/local? env h) (component-var? env h))))

     (def ^:private hof-names
       "Core functions that call their first argument, a function,
        synchronously or lazily."
       '#{apply map mapv filter filterv remove keep keep-indexed map-indexed mapcat
          reduce reduce-kv run! some every? not-any? not-every?
          sort-by group-by partition-by take-while drop-while repeatedly})

     (def ^:private lazy-names
       "Core functions whose result realizes the calls of its function argument later."
       '#{map filter remove keep keep-indexed map-indexed mapcat partition-by
          take-while drop-while repeatedly})

     (declare component-call-in?)

     (defn- fn-form? [env x]
       (and (seq? x)
            (or (= 'fn* (first x))
                (#{'clojure.core/fn 'cljs.core/fn} (ms/head-name env (first x))))))

     (defn- fn-calls-component?
       "Whether a function literal calls a possible component in its body."
       [env [_ & tail]]
       (let [tail (if (symbol? (first tail)) (rest tail) tail)
             arities (if (vector? (first tail)) [tail] tail)]
         (boolean (some (fn [[params & body]]
                          (component-call-in? (ioc/bind-locals env (ioc/binding-symbols params))
                                              (cons 'do body)))
                        arities))))

     (defn- seq-macro
       "The core sequence macro `x` calls (:for or :doseq), or nil."
       [env x]
       ({'clojure.core/for :for 'cljs.core/for :for 'clojure.core/doseq :doseq 'cljs.core/doseq :doseq}
        (ms/head-name env (first x))))

     (defn- indirect-call?
       "Whether call `x` calls a possible component indirectly: it passes a
        component var or a function literal that calls one, or a core
        higher-order function gets a local as its function; or it is a
        `for`/`doseq` whose bindings or body call one."
       [env x]
       (if (seq-macro env x)
         (component-call-in? env (cons 'do (rest x)))
         (let [q (ms/head-name env (first x))
               fs (when (and (core-name? q) (contains? hof-names (symbol (name q))))
                    (set (take (if (= "repeatedly" (name q)) 2 1) (rest x))))]
           (boolean (some (fn [a]
                            (cond (symbol? a) (if (ms/local? env a) (contains? fs a) (component-var? env a))
                                  (fn-form? env a) (fn-calls-component? env a)))
                          (rest x))))))

     (defn- component-call-in?
       "Whether `form` calls a possible component, directly or indirectly,
        in its own scope, outside DOM macros (they place their own
        children)."
       [env form]
       (boolean (ms/some-call env form
                              (fn [env x]
                                (let [h (first x)]
                                  (cond (dom-macro? env h) :org.replikativ.spindel.v2.macro-support/skip
                                        (component-head? env h) true
                                        (indirect-call? env x) true))))))

     (defn- lazy-call-in?
       "Whether `form` builds a lazy sequence of component calls in its own
        scope: it is realized later, outside any context."
       [env form]
       (boolean (ms/some-call env form
                              (fn [env x]
                                (let [h (first x) q (ms/head-name env h)]
                                  (cond (dom-macro? env h) :org.replikativ.spindel.v2.macro-support/skip
                                        (= :for (seq-macro env x)) (indirect-call? env x)
                                        (and (core-name? q) (contains? lazy-names (symbol (name q))))
                                        (indirect-call? env x)))))))

     (defn- deferred-call-in?
       "Whether `form` creates a computation or task in its own scope whose
        body calls a possible component: the body runs later, without the
        synchronous context."
       [env form]
       (boolean (ms/some-call env form
                              (fn [env x]
                                (cond (dom-macro? env (first x)) :org.replikativ.spindel.v2.macro-support/skip
                                      :else (when-let [body (ms/body-of env x)]
                                              (let [b (cons 'do body)]
                                                (or (component-call-in? env b) (deferred-call-in? env b)))))))))

     (defn- wrap [form]
       `(addr/call-with-context ~'__dom-parent ~'__dom-slot (fn [] ~form)))

     (defn- warn!
       "Prints ::unaddressed-call for `form`, once per location."
       [loc form why]
       (let [at (merge loc (select-keys (meta form) [:line :column]))]
         (when-not (contains? @warned at)
           (swap! warned conj at)
           (binding [*out* *err*]
             (println "WARNING:" ::unaddressed-call (pr-str at) "-" why
                      "- the call gets no DOM context; see the el/ namespace doc (el/in-context)")))))

     (defn- finish-as
       "`form`, an effect-free form or a form the rules do not take apart,
        classified as `shape` (the same call before its operands were
        hoisted): run under the context when it calls a possible component
        and is effect-free; warn when it cannot be placed."
       [env loc form shape]
       (let [calls? (component-call-in? env shape)
             eff? (v2/effectful? env shape)]
         (when (deferred-call-in? env shape)
           (warn! loc form "a computation or task created here calls a plain component in its body"))
         (when (lazy-call-in? env shape)
           (warn! loc form "a lazy sequence of component calls is realized later; use an eager form (mapv, into [])"))
         (cond
           (not calls?) form
           (not eff?) (wrap form)
           :else (do (warn! loc form "a plain component is called after a suspension in an unsupported form")
                     form))))

     (defn- finish [env loc form] (finish-as env loc form form))

     (declare treat)

     (defn- treat-from
       "`form` with every form after the first `n` treated."
       [env loc form n]
       (let [[head body] (split-at n form)]
         (with-meta (apply list (concat head (map #(treat env loc %) body))) (meta form))))

     (defn- treat-let [env loc [h bvec & body :as form]]
       (let [[bvec' env'] (loop [ps (partition 2 bvec) out [] env env]
                            (if-let [[b init] (first ps)]
                              (recur (rest ps) (conj out b (treat env loc init))
                                     (ioc/bind-locals env (ioc/binding-symbols b)))
                              [out env]))]
         (with-meta (apply list h bvec' (map #(treat env' loc %) body)) (meta form))))

     (defn- keep-in-place?
       "An operand that reads the same whenever it is evaluated: a local, a
        literal or a function literal (it reads vars only when called)."
       [env a]
       (or (and (symbol? a) (ms/local? env a))
           (and (not (symbol? a)) (not (coll? a)))
           (fn-form? env a)))

     (defn- hoist
       "A call: its operands are bound in order (each treated), except those
        that read the same at any time, then the call is finished. A var
        read is bound too, so it stays before a later operand that mutates
        the var or suspends. The call is classified as written, with its
        var operands, not as the locals they are bound to."
       [env loc [h & args :as form]]
       (if-not (or (component-call-in? env form) (deferred-call-in? env form))
         form
         (let [ts (mapv #(when-not (keep-in-place? env %) (gensym "arg")) args)
               env' (ioc/bind-locals env (remove nil? ts))
               call (with-meta (cons h (map #(or %1 %2) ts args)) (meta form))
               shape (with-meta (cons h (map (fn [t a] (if (and t (not (symbol? a))) t a)) ts args)) (meta form))]
           `(let [~@(mapcat (fn [t a] (when t [t (treat env loc a)])) ts args)]
              ~(finish-as env' loc call shape)))))

     (defn- treat
       "A form in a position whose value or effects the DOM context must
        reach (§2.5), in `env` where the reserved locals are bound."
       [env loc form]
       (cond
         (ms/body-of env form)
         (if (= 'org.replikativ.spindel.v2.core/spin (ms/head-name env (first form)))
           ;; an inline computation: its body is treated too, it captures the locals
           (with-meta (apply list (first form) (map #(treat env loc %) (rest form))) (meta form))
           (finish env loc form))

         (not (or (v2/effectful? env form) (deferred-call-in? env form)))
         (finish env loc form)

         (not (and (seq? form) (symbol? (first form))))
         (finish env loc form)

         :else
         (let [h (first form)]
           (cond
             (dom-macro? env h) form
             (ms/local? env h) (hoist env loc form)
             (ms/special? env h) (case h
                                   let* (treat-let env loc form)
                                   (do if) (treat-from env loc form 1)
                                   (finish env loc form))
             :else
             (let [q (ms/head-name env h)]
               (cond
                 ;; destructuring is lowered first: its defaults are code
                 (#{'clojure.core/let 'cljs.core/let} q)
                 (treat-let env loc (with-meta (first (ioc/expand-macro form env)) (meta form)))
                 (#{'clojure.core/when 'cljs.core/when 'clojure.core/when-not 'cljs.core/when-not} q)
                 (treat-from env loc form 1)
                 (or (and (ms/macro-meta env h) (not (inline-fn? env h))) (interop? h))
                 (finish env loc form)
                 :else (hoist env loc form)))))))

     (defn- context-bindings
       "Bindings of `p` and `s` to the current DOM context in `env`."
       [env loc p s]
       (if (addr/lexical-context? env)
         [p '__dom-parent s '__dom-slot]
         (let [c (gensym "context")]
           [c `(addr/current '~loc) p `(nth ~c 0) s `(nth ~c 1)])))

     (defn- source-loc
       "The location of `form`: its canonical source path (the same on every
        platform and compiler, D2), line and column."
       [env form]
       {:file (addr/source-file env)
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
                `(defmacro ~(with-meta nm {::dom-macro true :org.replikativ.spindel.v2.macro-support/scope :org.replikativ.spindel.v2.macro-support/transparent
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
   (defmacro ^{::dom-macro true :org.replikativ.spindel.v2.macro-support/scope :org.replikativ.spindel.v2.macro-support/transparent} element
     "An element with a dynamic tag: (element tag attrs? & children)."
     [tag & args]
     (element-form tag args &form &env)))

#?(:clj
   (defmacro ^{::dom-macro true :org.replikativ.spindel.v2.macro-support/scope :org.replikativ.spindel.v2.macro-support/transparent} in-context
     "The explicit boundary: runs the effect-free `body` under the current
      DOM context (the reserved locals, or the synchronous context), so a
      plain component called in it, also indirectly, is placed there.
      Usable after a suspension: (case (await mode) :a (el/in-context
      (card-a x)) ...). An effect in `body` is a compile error."
     [& body]
     (let [loc (source-loc &env &form)
           env (ioc/bind-locals &env reserved)]
       (when (v2/effectful? &env (cons 'do body))
         (throw (ex-info "el/in-context: its body must be effect-free; await before it" {:loc loc})))
       (when (deferred-call-in? env (cons 'do body))
         (warn! loc &form "a computation or task created here calls a plain component in its body"))
       (when (lazy-call-in? env (cons 'do body))
         (warn! loc &form "a lazy sequence of component calls is realized later; use an eager form (mapv, into [])"))
       (if (addr/lexical-context? &env)
         `(addr/call-with-context ~'__dom-parent ~'__dom-slot (fn [] ~@body))
         (let [c (gensym "context")]
           `(let [~c (addr/current '~loc)]
              (addr/call-with-context (nth ~c 0) (nth ~c 1) (fn [] ~@body))))))))

#?(:clj
   (defmacro ^{::dom-macro true :org.replikativ.spindel.v2.macro-support/scope :org.replikativ.spindel.v2.macro-support/opaque} component
     "A computation made by a plain component: (component body...) is a
      `spin` whose body is placed at the component's DOM context, captured
      as an input (moved, it reruns). Its body is treated like an element
      child: elements in it, and plain components it calls, also after a
      suspension in the supported shapes, are placed there. The spin keeps
      this form's source location as its creation site."
     [& body]
     (let [loc (source-loc &env &form)
           env (ioc/bind-locals &env reserved)
           spin-form (with-meta `(v2/spin ~@(map #(treat env loc %) body)) (meta &form))]
       (if (addr/lexical-context? &env)
         spin-form
         `(let [[~'__dom-parent ~'__dom-slot] (addr/current '~loc)]
            ~spin-form)))))
