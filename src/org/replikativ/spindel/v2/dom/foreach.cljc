(ns org.replikativ.spindel.v2.dom.foreach
  "Keyed lists on engine v2 (phase-d design §4.3).

  `(ifor-each key-fn coll render-fn)` renders the items of `coll` (a
  collection or an interval, read by its new value) to a KeyedFragment.
  Each item is a computation created under `(with-key fa)` and
  `(with-key k)`, `fa` the fragment's address and `k` the item's key: a
  later run of the enclosing computation adopts every item by its key, in
  any order, and reruns only an item whose captures changed (the item, by
  `identical?`, its keyed address, or a local the render fn uses). Two
  instances of one call site have different fragment addresses, so they
  never adopt each other's items.

  An item's DOM context is its keyed address `(keyed-child-address fa k)`,
  slot 0: its root keeps its address when the list reorders. A literal
  render fn `(fn [x] body...)` is inlined as the item's body, treated like
  an element child: it may track and await, and plain components it calls
  are placed. Any other render fn is called under the item's context,
  evaluated inside the item, so its free locals are captures. A render fn
  that returns a computation (`el/component`) is awaited.

  Keys must be distinct and neither nil nor false (`check-keys!`). Use
  `ifor-each` in a computation body: it awaits its items
  (`v2/await-all`, fail-fast: one failing item fails the list)."
  (:require [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.addressing :as addr]
            #?(:clj [org.replikativ.spindel.v2.dom.elements :as el])
            #?(:clj [org.replikativ.spindel.v2.macro-support :as ms])
            #?(:clj [is.simm.partial-cps.ioc :as ioc]))
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.dom.foreach])))

#?(:clj
   (defn- literal-fn
     "[param body] of `f` when it is an anonymous one-parameter function
      literal in `env`, else nil."
     [env f]
     (when (and (seq? f)
                (or (= 'fn* (first f))
                    (#{'clojure.core/fn 'cljs.core/fn} (ms/head-name env (first f)))))
       (let [tail (rest f)
             [params & body] (cond (vector? (first tail)) tail
                                   (and (= 1 (count tail)) (seq? (first tail)) (vector? (ffirst tail))) (first tail))]
         (when (and (vector? params) (= 1 (count params)) (not= '& (first params)))
           [(first params) body])))))

#?(:clj
   (defmacro ^{:org.replikativ.spindel.v2.dom.elements/dom-macro true} ifor-each
     "Renders the items of `coll` keyed by `key-fn` with `render-fn`; see the
      namespace doc."
     [key-fn coll render-fn]
     (let [loc (el/source-loc &env &form)
           [p s fa xs ks x k v] (map gensym '[parent slot fa xs ks x k v])
           item-env (ioc/bind-locals &env ['__dom-parent '__dom-slot x])
           body (if-let [[param fbody] (literal-fn &env render-fn)]
                  (el/treat item-env loc `(let [~param ~x] ~@fbody))
                  `(addr/call-with-context ~'__dom-parent ~'__dom-slot (fn [] (~render-fn ~x))))
           item (with-meta `(v2/spin (let [~v ~body] (if (v2/handle? ~v) (v2/await ~v) ~v))) (meta &form))]
       `(let [~@(el/context-bindings &env loc p s)
              ~fa (addr/element-address '~loc ~p ~s)
              ~xs (iv/get-new (iv/as-interval ~coll))
              ~ks (mapv ~key-fn ~xs)]
          (addr/check-keys! ~ks)
          (assoc (frag/keyed-fragment
                  (v2/await-all
                   (v2/with-key ~fa
                     (mapv (fn [~x ~k]
                             (v2/with-key ~k
                               (let [~'__dom-parent (addr/keyed-child-address ~fa ~k)
                                     ~'__dom-slot 0]
                                 ~item)))
                           ~xs ~ks))))
                 :addr ~fa :keys ~ks)))))
