(ns org.replikativ.spindel.v2.incremental
  "Incremental combinators on engine v2 (phase-d design §4.2-§4.4).

  `imap`, `ifilter`, `ireduce` and `islice` are plain functions with no
  per-call-site state. Each output is a typed interval: the transformation
  of the input interval's endpoints under the parameters of this call.
  `:new` comes from the input's new value, `:old` from its old value (nil
  when the input has none), `:deltas` is the output algebra's state-diff
  from `:old` to `:new` (nil without `:old`). Input deltas are not read.

  `:old` equals the previous output of the same call site only while the
  parameters stay the same between the two runs: the same pure function
  objects with the same captured values, the same `init`, the same window.
  When a parameter may change, and for any interval another computation
  returned, `:old` and `:deltas` are advisory: compare `:old` with what you
  last saw, or diff. Only `track` on a source gives engine-guaranteed
  deltas.

  `for-keyed` is the keyed memo map: one computation per item, created
  under `v2/with-key`, so a later run adopts each item's computation by
  its key, in any order, and reruns only the items whose captures changed."
  (:require [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.incremental.algebra :as a]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.incremental.sequence-algebra :as sa])
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.incremental])))

(defn- typed
  "The typed interval of `algebra` from the endpoints `old` and `new` of an
   input through `f`; `old` nil means the input has none."
  [algebra f old new]
  (if (nil? old)
    {:algebra algebra :old nil :new (f new) :deltas nil}
    (let [o (f old) n (f new)]
      {:algebra algebra :old o :new n :deltas (a/state-diff algebra o n)})))

(defn- endpoints [in]
  (let [i (iv/as-interval in)] [(iv/get-old i) (iv/get-new i)]))

(defn imap
  "`f` over the input sequence: `(mapv f new)`, `(mapv f old)`. Output
   algebra: sequence."
  [f in]
  (let [[o n] (endpoints in)] (typed sa/sequence-algebra #(mapv f %) o n)))

(defn ifilter
  "The items of the input sequence for which `p` is truthy: `(filterv p
   new)`, `(filterv p old)`. Output algebra: sequence."
  [p in]
  (let [[o n] (endpoints in)] (typed sa/sequence-algebra #(filterv p %) o n)))

(defn ireduce
  "The input sequence folded with `rf` from `init`. Output algebra:
   scalar."
  [rf init in]
  (let [[o n] (endpoints in)] (typed a/scalar-algebra #(reduce rf init %) o n)))

(defn- clamped-slice [v {:keys [start end] :or {start 0 end 0}}]
  (let [len (count v)
        s (max 0 (min start len))
        e (max s (min end len))]
    (if (= s e) [] (subvec (vec v) s e))))

(defn islice
  "The window `[start, end)` of the input sequence, bounds clamped. `window`
   is a map `{:start :end}` (its own old value) or an interval of one: the
   new slice is taken by the window's new value, the old slice by its old
   value; a window without an old value gives no `:old`. Output algebra:
   sequence."
  [window in]
  (let [[o n] (endpoints in)
        wo (iv/get-old window)
        wn (iv/get-new window)]
    (if (or (nil? o) (nil? wo))
      {:algebra sa/sequence-algebra :old nil :new (clamped-slice n wn) :deltas nil}
      (let [os (clamped-slice o wo) sn (clamped-slice n wn)]
        {:algebra sa/sequence-algebra :old os :new sn :deltas (a/state-diff sa/sequence-algebra os sn)}))))

#?(:clj
   (defmacro for-keyed
     "`(for-keyed [x coll :key key-fn] body...)`: the results of `body` for
      each item `x` of `coll` (a collection or an interval, read by its new
      value), in `coll` order. Each item's body is a computation created
      under `(v2/with-key (key-fn x))`: a later run of the enclosing
      computation adopts it by its key, in any order, and reruns it only
      when its captures changed (the item, by `identical?`, or another
      local the body uses). Use it in a computation body: it awaits the
      items (`v2/await-all`, fail-fast). Equal keys are not an error; they
      are positional within the key. The item computations keep this
      form's source location as their creation site; two invocations of a
      helper containing it are told apart by their creators or by an
      enclosing `with-key`."
     [[x coll & opts] & body]
     (let [{kf :key} (apply hash-map opts)
           xs (gensym "xs") k (gensym "kf") item (gensym "x")]
       (when-not kf
         (throw (ex-info "for-keyed needs :key: (for-keyed [x coll :key key-fn] body...)" {:form &form})))
       `(let [~xs (iv/get-new (iv/as-interval ~coll))
              ~k ~kf]
          (v2/await-all
           (mapv (fn [~item]
                   (v2/with-key (~k ~item)
                     ~(with-meta `(v2/spin (let [~x ~item] ~@body)) (meta &form))))
                 ~xs))))))
