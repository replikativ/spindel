(ns org.replikativ.spindel.incremental.combinators
  "Incremental combinators on the typed delta algebra.

   Each combinator follows the same skeleton (`with-cache`):

     - retrieve previous output (a typed-interval map) at this
       source-loc's address;
     - coerce the source to a PInterval and read its `:new`;
     - compute the new value as a *pure function* of source-new (and
       any free vars). `:new` is authoritative; source `:deltas` are
       advisory hints only.
     - derive a delta in the output algebra. The strategy that
       satisfies the four monoid laws for every combinator is
       *state-diff against the cached previous output*. When the
       source declares verified-no-change AND a cache exists, emit
       the algebra's empty deltas (the verified-no-change marker).

   Combinator surface
   ------------------

   - `map*`     — `Seq T → Seq U` via `f`. Output algebra: sequence.
   - `filter*`  — `Seq T → Seq T` via `pred`. Output algebra: sequence.
   - `reduce*`  — `Seq T → U`     via `rf`/`init`. Output algebra: scalar.
   - `slice*`   — windowed view `Seq T → Seq T`. Output algebra: sequence.
   - `for-each*`— `Seq T → Seq U` via `transform-fn`, memoised by
                  `key-fn`. Output algebra: sequence. The memoisation
                  is the entire reason this primitive exists; in every
                  other respect it is `map*`.

   The applicative (`izip*`) and monadic (`iflat-map*`) primitives live
   in `typed_combinators.cljc` alongside this namespace; they complete
   the algebraic core.

   Intervals
   ---------
   Combinators consume any value that satisfies `PInterval` (legacy
   `iv/Interval`, typed-interval maps, deltaable collections, or plain
   values via `as-interval`'s Object extension). They *produce* typed-
   interval maps with explicit `{:algebra :old :new :deltas}` keys.
   These maps interoperate with `iv/get-new` / `:new` / destructuring;
   downstream code never needs to distinguish.

   Caching
   -------
   Each call site has a stable address derived from `source-loc`.
   Previous output is stored at `[:incremental address]` in the
   execution context. The macro layer (`imap`, `ifilter`, etc.)
   captures `&form` metadata into `source-loc` so each call site gets
   its own address."
  (:refer-clojure :exclude [filter map reduce])
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.incremental.algebra :as a]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.incremental.sequence-algebra :as sa]))

;; =============================================================================
;; Address-based caching scaffold
;; =============================================================================

(defn- combinator-address
  "Stable address derived from a source-loc map. Same source-loc → same
   address; addresses don't collide across files or call sites."
  [source-loc]
  (keyword (str "comb-" (:file source-loc) "-" (:line source-loc) "-" (:column source-loc))))

(defn- prev-output [addr] (ec/get-state [:incremental addr]))
(defn- store-output! [addr v] (ec/swap-state! [:incremental addr] (constantly v)) v)

(defn- with-cache [source-loc compute-fn]
  (let [addr (combinator-address source-loc)
        prev (prev-output addr)
        out  (compute-fn prev)]
    (store-output! addr out)
    out))

;; =============================================================================
;; Sequence-algebra output builders
;; =============================================================================

(defn- seq-no-change
  "Verified-no-change typed interval over the cached value."
  [cached-new]
  {:algebra sa/sequence-algebra
   :old     cached-new
   :new     cached-new
   :deltas  (a/empty-deltas sa/sequence-algebra {:size (count cached-new)})})

(defn- seq-result
  "Build a sequence-algebra typed interval, deriving deltas via
   state-diff against `prev-new` when present. With no cache, deltas
   are `nil` (consumer recomputes)."
  [prev-new new-value]
  {:algebra sa/sequence-algebra
   :old     prev-new
   :new     new-value
   :deltas  (when prev-new
              (a/state-diff sa/sequence-algebra prev-new new-value))})

(defn- scalar-result
  "Build a scalar-algebra typed interval. `:deltas` is `::no-change`
   when the value equals prev-new; otherwise `[::replace new-value]`."
  [prev-new new-value]
  {:algebra a/scalar-algebra
   :old     prev-new
   :new     new-value
   :deltas  (cond
              (nil? prev-new)         nil
              (= prev-new new-value)  (a/empty-deltas a/scalar-algebra)
              :else                   (a/scalar-replace new-value))})

;; =============================================================================
;; map*
;; =============================================================================

(defn ^:no-doc map*
  "Apply `f` to every element of the source sequence. Output algebra:
   sequence."
  [source-loc f source]
  (with-cache source-loc
    (fn [prev]
      (let [src     (iv/as-interval source)
            src-new (iv/get-new src)]
        (if (and prev (iv/no-change? src))
          (seq-no-change (:new prev))
          (seq-result (:new prev) (mapv f src-new)))))))

(defn ^:no-doc map [f source]
  ;; Static-source convenience: synthesise a source-loc from a stable
  ;; tag. Discouraged for production — prefer the `imap` macro.
  (map* {:file "unknown" :line 0 :column 0} f source))

;; =============================================================================
;; filter*
;; =============================================================================

(defn ^:no-doc filter*
  "Retain elements of the source sequence for which `pred` returns
   truthy. Output algebra: sequence."
  [source-loc pred source]
  (with-cache source-loc
    (fn [prev]
      (let [src     (iv/as-interval source)
            src-new (iv/get-new src)]
        (if (and prev (iv/no-change? src))
          (seq-no-change (:new prev))
          (seq-result (:new prev) (filterv pred src-new)))))))

(defn ^:no-doc filter [pred source]
  (filter* {:file "unknown" :line 0 :column 0} pred source))

;; =============================================================================
;; reduce*
;; =============================================================================

(defn ^:no-doc reduce*
  "Fold the source sequence with `rf` and `init`. Output algebra:
   scalar.

   The `enter-fn`/`exit-fn` pair from earlier iterations is gone — the
   new design recomputes the fold whenever the source isn't verified-
   no-change. For ordinary commutative monoids this is the same wall-
   clock work as the enter/exit version (one pass over source-new vs
   one pass over deltas), and the simplicity wins. Reducers with
   expensive `rf` can wrap their input in `for-each*` to memoise per
   element."
  [source-loc rf init source]
  (with-cache source-loc
    (fn [prev]
      (let [src     (iv/as-interval source)
            src-new (iv/get-new src)]
        (if (and prev (iv/no-change? src))
          {:algebra a/scalar-algebra
           :old     (:new prev)
           :new     (:new prev)
           :deltas  (a/empty-deltas a/scalar-algebra)}
          (scalar-result (:new prev)
                         (clojure.core/reduce rf init src-new)))))))

(defn ^:no-doc reduce
  ([rf init source]
   (reduce* {:file "unknown" :line 0 :column 0} rf init source)))

;; =============================================================================
;; slice*
;; =============================================================================

(defn- subvec-safe [v start end]
  (let [len (count v)
        s (max 0 (min start len))
        e (max s (min end len))]
    (if (= s e) [] (subvec v s e))))

(defn ^:no-doc slice*
  "Positional window: items from source in `[start, end)`. Window may be
   a static map `{:start :end}` or a PInterval carrying such a map."
  [source-loc window source]
  (with-cache source-loc
    (fn [prev]
      (let [win-new (if (satisfies? iv/PInterval window)
                      (iv/get-new window)
                      window)
            src     (iv/as-interval source)
            src-new (iv/get-new src)
            slice   (subvec-safe src-new (:start win-new 0) (:end win-new 0))]
        (if (and prev (iv/no-change? src)
                 (= win-new (:window (meta prev))))
          (seq-no-change (:new prev))
          (let [out (seq-result (:new prev) slice)]
            ;; Stash the window so subsequent calls can detect no-change.
            (with-meta out {:window win-new})))))))

(defn ^:no-doc slice [window source]
  (slice* {:file "unknown" :line 0 :column 0} window source))

;; =============================================================================
;; for-each*
;;
;; map* with per-element memoisation: when `(= (key-fn t-now) (key-fn
;; t-prev))` AND the inputs compare equal, reuse the previous
;; transformed output. This is the right primitive for rendering lists
;; where `transform-fn` is expensive (building vnodes, creating TipTap
;; editors, etc.).
;;
;; The output algebra is sequence; deltas come from state-diff like the
;; other combinators.
;; =============================================================================

(defn ^:no-doc for-each*
  "Apply `transform-fn` to every element of the source sequence,
   memoising results by `key-fn`. Input-equal items at the same key
   reuse the prior `transform-fn` output. Output algebra: sequence.

   Note: `key-fn` is used for memoisation only. The output `:deltas`
   come from `state-diff` on the transformed vectors — a *value-based*
   sequence diff that does not recognise reorders (a reorder degrades to
   change-everything). A consumer that needs a reorder-aware keyed diff
   should use `sequence-algebra/keyed-seq-diff` — which is what the DOM
   `dom/foreach` layer does."
  [source-loc key-fn transform-fn source]
  (with-cache source-loc
    (fn [prev]
      (let [src     (iv/as-interval source)
            src-new (iv/get-new src)]
        (if (and prev (iv/no-change? src))
          (seq-no-change (:new prev))
          (let [prev-by-key (:by-key (meta prev) {})
                [new-by-key new-vec]
                (clojure.core/reduce
                 (fn [[bk vs] item]
                   (let [k (key-fn item)
                         [prev-input prev-output] (get prev-by-key k)
                         transformed (if (and (some? prev-input) (= prev-input item))
                                       prev-output
                                       (transform-fn item))]
                     [(assoc bk k [item transformed])
                      (conj vs transformed)]))
                 [{} []]
                 src-new)
                out (seq-result (:new prev) new-vec)]
            (with-meta out {:by-key new-by-key})))))))

(defn ^:no-doc for-each [key-fn transform-fn source]
  (for-each* {:file "unknown" :line 0 :column 0} key-fn transform-fn source))

;; =============================================================================
;; Macros — capture source-loc from caller for stable per-call-site addressing.
;; =============================================================================

#?(:clj
   (defmacro imap
     "Incremental map: `(imap f source)`."
     [f source]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(map* ~source-loc ~f ~source))))

#?(:clj
   (defmacro ifilter
     "Incremental filter: `(ifilter pred source)`."
     [pred source]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(filter* ~source-loc ~pred ~source))))

#?(:clj
   (defmacro ireduce
     "Incremental reduce: `(ireduce rf init source)`. The 5-arg form
      from the previous iteration (with explicit enter/exit fns) is
      removed; the new implementation recomputes the fold from source-
      new whenever there's any change. Wrap an expensive `rf`'s input
      in `for-each*` for per-element memoisation."
     [rf init source]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(reduce* ~source-loc ~rf ~init ~source))))

#?(:clj
   (defmacro islice
     "Incremental slice: `(islice {:start :end} source)`."
     [window source]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(slice* ~source-loc ~window ~source))))

#?(:clj
   (defmacro ifor-each
     "Incremental keyed map: `(ifor-each key-fn transform-fn source)`."
     [key-fn transform-fn source]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(for-each* ~source-loc ~key-fn ~transform-fn ~source))))
