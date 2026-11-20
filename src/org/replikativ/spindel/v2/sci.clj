(ns org.replikativ.spindel.v2.sci
  "Engine v2 bodies in SCI (dvergr port step 6a).

   `install!` gives an SCI context the v2 body surface in the SCI namespace
   `org.replikativ.spindel.v2.core`: the macros `spin`, `task`, `task-with`,
   `aseq`, `with-scope` and `with-path`, and the effects `await`, `track`,
   `await-all`, `await-any`, `take!`, `acquire!`, `offload`, `external`,
   `await-op`, `sleep` and `savepoint`. `expose-effect!` adds effects the host
   registered with `v2/register-effect!`.

   **Expansion.** The macros are host functions run by SCI's macroexpander.
   They take the body apart as the host macros do (`register-finally`, the
   captured inputs, the creation site), with SCI's resolution, and invert it
   with partial-cps's `ioc/invert`, interpreted in the context so that names
   resolve against SCI's namespaces. Captured inputs are the locals in `&env`
   that occur in the body's text. The compiler is read-only to interpreted
   code: the installed vars and ioc's are `:sci/built-in`, the breakpoint
   handler is a value, not a name, and `ns-unmap`, `intern` and `remove-ns`
   refuse the installed namespaces (`guard-mappings!`). A `def` of a new name
   inside one is still possible: SCI has no namespace-level guard.

   **No engine internals in SCI.** The expansion calls host functions that
   are spliced into the code as values; no SCI namespace names them. They are
   still reachable as values (`macroexpand` shows them), so each one acts
   only on the calling run and returns no row, world or scope: a scope or
   saved path is an opaque value bound to the run (and world) that opened it
   and refused elsewhere; the finally-region functions act only balanced,
   and a body's completion closes regions its code left open. A custom
   effect is called through a function bound to its one exposed symbol.

   **Resume adapter (H-body).** Every body and every continuation handed to
   the engine is wrapped. At the start of a slice the wrapper selects the
   interpreter for the world being processed (`(select world interpreter)`,
   see `set-resolver!`; without a resolver, the interpreter the code was
   captured in), copies the SCI continuation context captured at the effect
   site (or at creation, for a body) onto it, and runs the code there with
   the SCI bindings of that point; it forces the code's trampoline Thunks
   inside. A continuation called synchronously within a slice its run
   already runs in the adapter is called directly. So a body inherited by a
   fork resumes against the heap the resolver names for the fork, and SCI
   `binding`s that span an effect are restored on whichever thread resumes.

   **Refusal.** When the resolver returns nil, or the interpreter cannot be
   entered (another lineage, retired), the run fails without running SCI
   code; its open finally regions are dropped (their finalizers are SCI
   code), so it retires.

   **No waiting in a slice (B7).** The interpreter's gate (SCI forks and
   retirement take it exclusively) is taken with `tryLock`, which passes a
   queued fork. While a fork or retirement holds it, or the resolver returns
   a pending interpreter, the run parks and the slice is retried; a run that
   is unwinding a cancellation cannot park, so its finalizers are dropped.
   This reads SCI's internal gate field; SCI has no public non-blocking
   entry."
  (:require [clojure.java.io :as io]
            [is.simm.partial-cps.runtime :as pr]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.rows :as rw]
            [sci.core :as sci]
            [sci.ctx-store :as store]))

(set! *warn-on-reflection* true)

(def ^:private core-ns 'org.replikativ.spindel.v2.core)

;; ---------------------------------------------------------------------------
;; Interpreter selection

(defn- lineage [ctx]
  (or (:sci.impl/lineage ctx)
      (throw (ex-info "v2.sci needs a forkable SCI context (:runtime-mode :forkable)"
                      {:type ::not-forkable}))))

(defn- config
  "The configuration `install!` stored in `ctx` (forks share it)."
  [ctx]
  (or (::config @(:env ctx))
      (throw (ex-info "v2.sci is not installed in this SCI context" {:type ::not-installed}))))

;; [world run regions] of the adapter running on this thread; `regions` is
;; [open-finally-regions in-finally-clauses] of the run as SCI code changed
;; them through the spliced functions (the engine's R-FINS and R-INFIN)
(def ^:private ^ThreadLocal adapting (ThreadLocal.))

(defn- regions
  "The region counts of the run on this thread, when the adapter runs it."
  ^longs []
  (when-let [^objects a (.get adapting)]
    (when (and (identical? (aget a 0) (v2/cw)) (identical? (aget a 1) (v2/active-run)))
      (aget a 2))))

(defn- close-regions!
  "Drops the run's open regions, whose SCI code cannot run (refusal) or which
   SCI code left open (completion), so the run can retire."
  [^longs b]
  (dotimes [_ (aget b 1)] (v2/leave-finalizer!))
  (dotimes [_ (aget b 0)] (v2/exit-finally!) (v2/leave-finalizer!))
  (aset b 0 0)
  (aset b 1 0))

(defn- capture
  "[interpreter continuation-context fins infins] of the SCI code running
   now. The interpreter is SCI's current context when it belongs to `home`'s
   lineage, else `home` (a host thread calling an SCI function). A body
   (`body? true`) starts with no open region; a continuation with the run's."
  [home body?]
  (let [cur store/*ctx*
        ctx (if (and cur (identical? (:sci.impl/lineage cur) (:sci.impl/lineage home))) cur home)
        b (when-not body? (regions))]
    [ctx (sci/capture-continuation-context ctx) (if b (aget b 0) 0) (if b (aget b 1) 0)]))

(defn- select
  "The interpreter to run captured code of `ctx` in, for the world being
   processed, or a pending value (the resolver prepares it off the slice)."
  [cfg ctx]
  (if-let [f (:select @cfg)]
    (let [x (f (v2/cw) ctx)]
      (cond (nil? x) (throw (ex-info "no SCI interpreter for this world" {:type ::no-interpreter}))
            (and (instance? clojure.lang.IPending x) (realized? x)) @x
            :else x))
    ctx))

(defn- pending? [x] (and (instance? clojure.lang.IPending x) (instance? clojure.lang.IDeref x)))

(defn- read-gate
  "The read side of the gate SCI's forks and retirement take exclusively."
  ^java.util.concurrent.locks.Lock [ctx]
  (.readLock ^java.util.concurrent.locks.ReentrantReadWriteLock
   (.-gate ^sci.impl.world.DenseWorld (:sci.impl/world ctx))))

(defn- off-slice
  "Runs `f` on a new virtual thread: host work that may wait."
  [f]
  (Thread/startVirtualThread ^Runnable (fn [] (f))))

(defn- force-all [x]
  (loop [x x] (if (pr/thunk? x) (recur (pr/force-thunk x)) x)))

(def ^:private recorded-callstacks (delay @(requiring-resolve 'sci.impl.utils/recorded-callstacks)))

(defn- unwrap
  "The exception SCI code threw. On the thread that created the context,
   outside an SCI `try`, SCI wraps an exception leaving interpreted code with
   its location. Resumed code runs outside its lexical `try` (CPS: the
   engine routes the throw to the suspension's handler), so the wrapper
   would reach the body's `catch` on that thread only."
  [t]
  ;; SCI records the callstack of the exception it wraps (`sci.impl.utils/
  ;; recorded-callstacks`, by identity); its wrapper carries that same
  ;; callstack. An exception user code throws is never replaced.
  (let [cause (ex-cause t)
        st (:sci.impl/callstack (ex-data t))]
    (if (and cause st (identical? st (.get ^java.util.Map @recorded-callstacks cause)))
      cause
      t)))

;; [world run refusal] of the last refusal on this thread
(def ^:private ^ThreadLocal refusing (ThreadLocal.))

(defn- refuse!
  "The run's SCI code cannot run here: its open regions are dropped (their
   finalizers are SCI code) and the slice fails, so the run fails and
   retires without running SCI code. The engine routes a throw from a
   resumed continuation to its error continuation; that one recognizes this
   refusal (`refused-here?`) and passes it on without entering SCI."
  [b t]
  (close-regions! b)
  (let [e (if (#{::no-interpreter ::interpreter-busy} (:type (ex-data t)))
            t
            (ex-info "no SCI interpreter for this world" {:type ::no-interpreter} t))]
    (.set refusing (doto (object-array 3) (aset 0 (v2/cw)) (aset 1 (v2/active-run)) (aset 2 e)))
    (throw e)))

(defn- refused-here?
  "Whether `e` is the refusal of the run on this thread just thrown (not
   another run's refusal this run awaited, which its code may catch)."
  [e]
  (let [^objects a (.get refusing)]
    (and a (identical? e (aget a 2))
         (identical? (aget a 0) (v2/cw)) (identical? (aget a 1) (v2/active-run)))))

(defn- thunk-or-nil
  "What an effect returns to the body: a Thunk of its own code, else nothing."
  [x]
  (when (pr/thunk? x) x))

(declare in-run)

(defn- park!
  "The interpreter is not available without waiting (its gate is held
   exclusively, or the resolver is still preparing it). A slice never waits
   (B7): the run parks on an external resource that a virtual thread
   completes once `(wait)` returns, then the slice is tried again. A run that
   cannot park (it is unwinding a cancellation) is refused: its finalizers
   cannot run without waiting, so they are dropped."
  [cfg cap f on-error b wait]
  (let [refused (volatile! nil)
        parking (volatile! true)
        res (v2/external-effect!
             (fn [complete!]
               (off-slice #(do (try (wait) (catch Throwable _)) (complete! nil)))
               (fn [] :joined))
             (fn [_] (in-run cfg cap f on-error))
             (fn [e] (if @parking (vreset! refused e) (on-error e))))]
    (vreset! parking false)
    (if-let [e @refused]
      (refuse! b (ex-info "the SCI interpreter is held exclusively and the run cannot wait"
                          {:type ::interpreter-busy} e))
      (thunk-or-nil res))))

(defn- in-run
  "Runs `(f)` as code of the active run: in the interpreter selected for the
   processed world, with the SCI bindings and region counts of `cap`,
   forcing its Thunks. It never waits: see `park!`. `on-error` resumes the
   run's error path when a park ends in an error (cancellation)."
  [cfg [ctx cc fins infins :as cap] f on-error]
  (let [w (v2/cw)
        r (v2/active-run)
        ^objects prev (.get adapting)]
    (if (and r prev (identical? w (aget prev 0)) (identical? r (aget prev 1)))
      (f)
      (let [b (doto (long-array 2) (aset 0 (long fins)) (aset 1 (long infins)))
            target (try (select cfg ctx) (catch Throwable t (refuse! b t)))]
        (if (pending? target)
          (park! cfg cap f on-error b #(deref target))
          (let [^java.util.concurrent.locks.Lock gate (try (read-gate target) (catch Throwable t (refuse! b t)))]
            ;; tryLock barges past a queued fork (it waits for the evaluations
            ;; holding the gate, one of which may wait for this run); it fails
            ;; only while a fork or retirement holds the gate
            (if-not (.tryLock gate)
              (park! cfg cap f on-error b #(do (.lock gate) (.unlock gate)))
              (let [entered (volatile! false)]
                (.set adapting (doto (object-array 3) (aset 0 w) (aset 1 r) (aset 2 b)))
                (try
                  (let [run (sci/continuation-context-fn (sci/retarget-continuation-context cc target)
                                                         (fn [] (vreset! entered true) (force-all (f))))]
                    (run))
                  (catch Throwable t
                    (if @entered (throw (unwrap t)) (refuse! b t)))
                  (finally
                    (.set adapting prev)
                    (.unlock gate)))))))))))

(defn- settled
  "The engine continuation `k` (a body's ok or err): regions SCI code left
   open are closed first, so the completed run retires."
  [k]
  (fn [v]
    (when-let [b (regions)] (close-regions! b))
    (k v)))

(defn- run-in
  "`(f)` in the interpreter of `cap` with its SCI bindings; waits for the
   gate (host threads only)."
  [[ctx cc] f]
  (try ((sci/continuation-context-fn (sci/retarget-continuation-context cc ctx) f))
       (catch Throwable t (throw (unwrap t)))))

(defn- try-run-in
  "[`(f)`] as `run-in`, or nil without waiting when the gate is held."
  [[ctx :as cap] f]
  (let [gate (read-gate ctx)]
    (when (.tryLock gate)
      (try [(run-in cap f)] (finally (.unlock gate))))))

(defn- offload-fn
  "offload's `f`: on the world's executor, outside every world (may wait)."
  [cap f]
  (fn [] (run-in cap f)))

(defn- op-fn
  "await-op's op `(op ok err)`: started now, or off the executor's thread
   when the gate is held."
  [cap op]
  (fn [ok err]
    (when-not (try-run-in cap #(op ok err))
      (off-slice #(try (run-in cap (fn [] (op ok err))) (catch Throwable t (err t)))))
    nil))

(defn- cancel-fn
  "external's cancel fn `c`, called under the world gate: run now, or off
   the gate when the interpreter's gate is held (then the resource waits for
   the operation's completion; a deferred `:joined` completes it)."
  [cap c complete!]
  (fn []
    (if-let [[res] (try-run-in cap c)]
      res
      (do (off-slice #(when (= :joined (try (run-in cap c) (catch Throwable _ nil)))
                        (complete! (ex-info "cancelled" {:spindel/cancelled true}) true)))
          nil))))

(defn- external-fn
  "external's `(f complete!)`, called under the world gate: run now, or off
   the gate when the interpreter's gate is held."
  [cap f]
  (fn [complete!]
    (if-let [[c] (try-run-in cap #(f complete!))]
      (if (fn? c) (cancel-fn cap c complete!) c)
      (let [state (atom :pending)]        ; :pending | :cancelled | [:started c]
        (off-slice
         (fn []
           (when (= :pending @state)
             (let [c (try (run-in cap #(f complete!)) (catch Throwable t (complete! t true) nil))
                   [old] (swap-vals! state #(if (= :pending %) [:started c] %))]
               (when (and (= :cancelled old) (fn? c))
                 (try (run-in cap c) (catch Throwable _ nil)))))))
        (fn []
          (let [[old] (swap-vals! state #(if (= :pending %) :cancelled %))]
            (if (vector? old)
              (let [c (second old)] (if (fn? c) ((cancel-fn cap c complete!)) nil))
              :joined)))))))

;; ---------------------------------------------------------------------------
;; The functions the expansion calls (spliced as values)

(deftype ^:private Opaque [x run world])

(defn- opened
  "`x` (a scope or a saved path) for the active run in the processed world."
  [x]
  (Opaque. x (v2/active-run) (v2/cw)))

(defn- own
  "The value inside `o` when the active run opened it: the same run (by id)
   in the world that opened it or in a world derived from it that inherited
   `row` (a fork); else nil."
  [o row-of-x]
  (when (instance? Opaque o)
    (let [^Opaque o o
          r (v2/active-run) w (v2/cw) r0 (.-run o) w0 (.-world o)]
      (when (and r w r0 w0
                 (identical? (rw/g w rw/W-FAMILY) (rw/g w0 rw/W-FAMILY))
                 (= (rw/g r rw/ID) (rw/g r0 rw/ID))
                 (or (identical? w w0) (#'v2/inherited? w (or (row-of-x (.-x o)) r0))))
        (.-x o)))))

(defn- inputs [v] (if (empty? v) v2/empty-inputs (object-array v)))

(defn- abi
  "The host functions spliced into expansions for the lineage of `home`."
  [cfg home]
  (let [err* (fn [cap ek] (fn on-err [e]
                            (if (refused-here? e)
                              (do (.remove refusing) (throw e))   ; to the slice: the run fails
                              (in-run cfg cap #(ek e) on-err))))
        k* (fn [cap k ek] (let [e (err* cap ek)] (fn [v] (in-run cfg cap #(k v) e))))
        body* (fn [cap body] (fn [ok err] (in-run cfg cap #(body (settled ok) (settled err)) err)))
        fx (fn [native]
             (fn [x k ek]
               (let [cap (capture home false)]
                 (thunk-or-nil (native x (k* cap k ek) (err* cap ek))))))]
    {:create-comp (fn [site ins body]
                    (v2/create-comp! site (inputs ins) (body* (capture home true) body)))
     :spawn (fn
              ([site ins body] (v2/spawn! site (inputs ins) (body* (capture home true) body)))
              ([site ins body opts] (v2/spawn! site (inputs ins) (body* (capture home true) body) opts)))
     :new-aseq (fn [site ins step init]
                 (let [cap (capture home true)]
                   ;; `step` binds the state (destructuring, `:or` defaults): SCI
                   ;; code, so it runs inside the adapter with the element's body
                   (v2/new-aseq-at site (inputs ins) (fn [s] (body* cap (fn [ok err] ((step s) ok err)))) init)))
     :track (fx (fn [x k ek] (v2/track-effect! (v2/row-of x) k ek)))
     :await (fx (fn [x k ek] (v2/await-effect! (v2/row-of x) k ek)))
     :await-all (fx v2/await-all-effect!)
     :await-any (fx v2/await-any-effect!)
     :consume (fx (fn [x k ek] (v2/consume-effect! (v2/row-of x) k ek)))
     :sleep (fx v2/sleep-effect!)
     :offload (fn [f opts k ek]
                (let [cap (capture home false)]
                  (thunk-or-nil (v2/offload-effect! (offload-fn cap f) opts (k* cap k ek) (err* cap ek)))))
     :external (fn [f k ek]
                 (let [cap (capture home false)]
                   (thunk-or-nil (v2/external-effect! (external-fn cap f) (k* cap k ek) (err* cap ek)))))
     :await-op (fn [op opts k ek]
                 (let [cap (capture home false)]
                   (thunk-or-nil (v2/await-op-effect! (op-fn cap op) opts (k* cap k ek) (err* cap ek)))))
     :savepoint (fn [site payload k ek]
                  (let [cap (capture home false)]
                    (thunk-or-nil (v2/savepoint-effect! site payload (k* cap k ek) (err* cap ek)))))
     :custom (fn [sym]
               (fn [args site k ek]
                 (let [cap (capture home false)]
                   (thunk-or-nil (v2/custom-effect! sym args site (k* cap k ek) (err* cap ek))))))
     ;; balanced only: a region opens in a run the adapter runs and closes
     ;; only when one is open (B3; unbalanced calls change nothing)
     :enter-finally (fn [] (when-let [b (regions)] (v2/enter-finally!) (aset b 0 (inc (aget b 0)))) nil)
     :exit-finally (fn [] (when-let [b (regions)]
                            (when (pos? (aget b 0))
                              (v2/exit-finally!) (aset b 0 (dec (aget b 0))) (aset b 1 (inc (aget b 1)))))
                     nil)
     :leave-finalizer (fn [] (when-let [b (regions)]
                               (when (pos? (aget b 1))
                                 (v2/leave-finalizer!) (aset b 1 (dec (aget b 1)))))
                        nil)
     ;; a scope or saved path acts only in the run that opened it (refused,
     ;; with no effect, in another run or an unrelated world)
     :open-scope (fn [] (opened (v2/open-scope!)))
     :close-scope (fn [s] (when-let [x (own s identity)] (v2/close-scope-fx! x)) nil)
     :push-path (fn [p] (opened (v2/push-path! p)))
     :pop-path (fn [s] (when-let [x (own s (constantly nil))] (v2/pop-path! x)) nil)}))

;; ---------------------------------------------------------------------------
;; Expansion (SCI's resolution; mirrors the host body macros of v2.core)

(def ^:private builtin-effects
  "SCI name of each built-in effect -> its ABI key."
  {'track :track 'await :await 'await-all :await-all 'await-any :await-any
   'take! :consume 'acquire! :consume 'offload :offload 'external :external
   'await-op :await-op 'sleep :sleep 'savepoint :savepoint})

(def ^:private effect-arity
  {:track 1 :await 1 :await-all 1 :await-any 1 :consume 1 :offload 2 :external 1
   :await-op 2 :sleep 1 :savepoint 2})

(def ^:private body-macros
  (into #{} (map #(symbol (str core-ns) %)) ["spin" "task" "task-with" "aseq"]))

(def ^:private region-macros
  (into #{} (map #(symbol (str core-ns) %)) ["with-scope" "with-path"]))

(defn- sci-var
  "The SCI var `h` names in the namespace being compiled, unless `h` is a
   local or a special form."
  [env h]
  (when (and (symbol? h) (not (contains? env h)) (not (special-symbol? h)))
    (let [v (try (sci/resolve store/*ctx* h) (catch Exception _ nil))]
      (when (instance? sci.lang.Var v) v))))

(defn- var-sym [v]
  (let [m (meta v)]
    (when (and (:ns m) (:name m)) (symbol (str (:ns m)) (str (:name m))))))

(defn- opaque-head? [env h]
  (or (#{'quote 'fn 'fn* 'reify 'deftype 'proxy 'letfn 'letfn*} h)
      (contains? body-macros (some-> (sci-var env h) var-sym))))

(defn- has-finally? [env form]
  (and (seq? form)
       (or (and (= 'try (first form)) (some #(and (seq? %) (= 'finally (first %))) form))
           (and (not (opaque-head? env (first form))) (some #(has-finally? env %) form)))))

(defn- user-macro
  "The SCI macro var a form calls, unless it is one of ours."
  [env h]
  (when-let [v (sci-var env h)]
    (when (and (:macro (meta v)) (not (opaque-head? env h))
               (not (contains? region-macros (var-sym v))))
      v)))

(defn- realize
  "`form` with every seq a realized list: forkable SCI refuses host lazy
   sequences (the code syntax-quote and `map` build here)."
  [form]
  (cond (seq? form) (with-meta (apply list (map realize form)) (meta form))
        (record? form) form
        (vector? form) (with-meta (mapv realize form) (meta form))
        (map? form) (with-meta (into (empty form) (map (fn [[k v]] [(realize k) (realize v)])) form) (meta form))
        (set? form) (with-meta (into (empty form) (map realize) form) (meta form))
        :else form))

(defn- catch-or-finally? [x] (and (seq? x) (#{'catch 'finally} (first x))))

(defn- register-finally
  "§7 B3: each `try` with a `finally` registers its region with the run; a
   user macro whose expansion has one (`binding`, `with-open`, ...) is
   expanded so its region registers too. Nested bodies and closures are left
   alone."
  [{:keys [env] :as a} form]
  (let [rf #(register-finally a %)]
    (cond
      (seq? form)
      (let [h (first form)
            mv (user-macro env h)
            expanded (when mv (apply @mv form env (rest form)))]
        (cond
          (opaque-head? env h) form
          (and expanded (has-finally? env expanded)) (rf expanded)
          (= 'try h)
          (let [clauses (mapv rf (rest form))
                [body cfs] (split-with (complement catch-or-finally?) clauses)]
            (if (some #(= 'finally (first %)) cfs)
              (with-meta
                `(~'try (do (~(:enter-finally a)) ~@body)
                        ~@(map (fn [c] (if (= 'finally (first c))
                                         (list 'finally (list (:exit-finally a))
                                               (list 'try (cons 'do (rest c)) (list 'finally (list (:leave-finalizer a)))))
                                         c))
                               cfs))
                (meta form))
              (with-meta (cons 'try clauses) (meta form))))
          :else (with-meta (apply list (map rf form)) (meta form))))
      (vector? form) (with-meta (mapv rf form) (meta form))
      (map? form) (with-meta (into {} (map (fn [[k v]] [(rf k) (rf v)])) form) (meta form))
      (set? form) (with-meta (into #{} (map rf) form) (meta form))
      :else form)))

(defn- captured
  "The locals of `env` that occur in `body`, sorted: the captured inputs."
  [env body]
  (let [acc (volatile! #{})]
    (letfn [(walk [x]
              (cond (symbol? x) (when (contains? env x) (vswap! acc conj x))
                    (map? x) (doseq [[k v] x] (walk k) (walk v))
                    (coll? x) (run! walk x)))]
      (walk body))
    (vec (sort-by str @acc))))

(defn- site-of [form]
  (bit-and 0x3fffffff (hash [(str @sci/ns) (:line (meta form)) (:column (meta form))])))

(defn- breakpoints [cfg]
  (let [h (:bp @cfg)]
    (into {} (map (fn [s] [s h]))
          (concat (map #(symbol (str core-ns) (str %)) (keys builtin-effects))
                  (keys (:effects @cfg))))))

(defn- body-fn-form [cfg a env body]
  (let [r (gensym "r") e (gensym "e")
        params {:r r :e e :env env :breakpoints (breakpoints cfg) :opaque-scopes body-macros}]
    (realize `(fn [~r ~e] ~((:invert @cfg) params (realize (register-finally (assoc a :env env) (cons 'do body))))))))

(defn- bp
  "The breakpoint handler of every effect: a value in the breakpoint map, not
   a name SCI code could rebind (see `load-ioc!`)."
  [cfg a]
  (fn [ictx r e]
    (let [form (:form ictx)
          sym (var-sym (sci-var (:env ictx) (first form)))]
      (fn [args]
        (realize
         (if-let [k (builtin-effects (when (= (str core-ns) (namespace sym)) (symbol (name sym))))]
          ;; as the host emitters destructure their arguments
           `(~(a k) ~@(take (effect-arity k) (concat args (repeat nil))) ~r ~e)
           (if-let [f (get (:effects @cfg) sym)]
             `(~f [~@args] ~(site-of form) ~r ~e)
             (throw (ex-info "not an exposed effect" {:effect sym})))))))))

(defn- macros [cfg a]
  (update-vals
   {'spin (fn [form env & body]
            (list (:create-comp a) (site-of form) (captured env body) (body-fn-form cfg a env body)))
    'task (fn [form env & body]
            (list (:spawn a) (site-of form) (captured env body) (body-fn-form cfg a env body)))
    'task-with (fn [form env opts & body]
                 (list (:spawn a) (site-of form) (captured env body) (body-fn-form cfg a env body) opts))
    'aseq (fn [form env [s init] & body]
            (let [env' (into env (map (fn [x] [x true])) (take-nth 2 (destructure [s nil])))]
              (list (:new-aseq a) (site-of form) (captured env (list 'fn [s] (cons 'do body)))
                    (list `fn [s] (body-fn-form cfg a env' body)) init)))
    'with-scope (fn [_form _env & body]
                  (let [s (gensym "scope")]
                    `(let [~s (~(:open-scope a))]
                       (~'try (do (~(:enter-finally a)) ~@body)
                              (~'finally (~(:exit-finally a))
                                         (~'try (~(:close-scope a) ~s) (~'finally (~(:leave-finalizer a)))))))))
    'with-path (fn [_form _env p & body]
                 (let [saved (gensym "path")]
                   `(let [~saved (~(:push-path a) ~p)]
                      (~'try (do (~(:enter-finally a)) ~@body)
                             (~'finally (~(:exit-finally a))
                                        (~'try (~(:pop-path a) ~saved) (~'finally (~(:leave-finalizer a)))))))))}
   (fn [m] (fn [& args] (realize (apply m args))))))

(defn- outside [n] (fn [& _] (throw (ex-info (str n " outside a body") {:type ::outside-body}))))

;; ---------------------------------------------------------------------------
;; Installation

(defn- guard-mappings!
  "SCI guards the root and metadata of `:sci/built-in` vars, not namespace
   mappings: `ns-unmap`, `intern` and `remove-ns` change them for every
   later evaluation. This replaces those three in the context's
   `clojure.core` with versions that refuse to touch the installed
   namespaces (`:protected` in `cfg`: namespace symbols, and qualified
   symbols of single exposed effects) and otherwise do what SCI's do."
  [ctx cfg]
  (let [[unmap intern* remove-ns*] (sci/eval-string* ctx "[clojure.core/ns-unmap clojure.core/intern clojure.core/remove-ns]")
        core (sci/create-ns 'clojure.core)
        ns-sym (fn [x] (symbol (str x)))
        protected? (fn [n sym]
                     (let [ps (:protected @cfg)]
                       (or (contains? ps n) (and sym (contains? ps (symbol (str n) (str sym)))))))
        refuse (fn [n] (throw (ex-info (str "The mappings of namespace " n " are read-only.")
                                       {:type ::read-only-namespace :ns n})))]
    (sci/add-namespace!
     ctx 'clojure.core
     {'ns-unmap (sci/new-var 'ns-unmap (fn [n sym] (if (protected? (ns-sym n) sym) (refuse (ns-sym n)) (unmap n sym)))
                             (read-only core))
      'intern (sci/new-var 'intern (fn
                                     ([n sym] (if (protected? (ns-sym n) sym) (refuse (ns-sym n)) (intern* n sym)))
                                     ([n sym v] (if (protected? (ns-sym n) sym) (refuse (ns-sym n)) (intern* n sym v))))
                           (read-only core))
      'remove-ns (sci/new-var 'remove-ns (fn [n]
                                           (let [n' (ns-sym n)]
                                             (if (or (protected? n' nil)
                                                     (some #(= (str n') (namespace %)) (filter qualified-symbol? (:protected @cfg))))
                                               (refuse n')
                                               (remove-ns* n))))
                              (read-only core))})))

(defn- read-only
  "Var metadata SCI refuses to redefine, `alter-var-root` or `alter-meta!`
   (`:sci/built-in`): code in the interpreter cannot change how later bodies
   compile."
  [ns-obj]
  {:ns ns-obj :sci/built-in true})

(def ^:private ioc-handler-lookup
  ["(let [handler (resolve (breakpoints (var-name env head)))"
   "(let [handler (let [h (breakpoints (var-name env head))] (if (symbol? h) (resolve h) h))"])

(defn- load-ioc!
  "Loads partial-cps's `ioc` into `ctx` and returns its `invert`. The
   breakpoint handler is a value in the map (no name to rebind), every ioc
   var is made read-only, and its macro-time registries (binding restorers
   and scopes) are fixed empty: interpreted code cannot change the compiler."
  [ctx]
  (let [src (slurp (io/resource "is/simm/partial_cps/ioc.clj"))
        [from to] ioc-handler-lookup]
    (when-not (= 1 (count (re-seq (re-pattern (java.util.regex.Pattern/quote from)) src)))
      (throw (ex-info "partial-cps ioc changed: the breakpoint handler lookup is not where v2.sci expects it"
                      {:type ::incompatible-partial-cps})))
    (sci/eval-string* ctx (.replace ^String src ^String from ^String to))
    (sci/eval-string* (assoc ctx :unrestricted true)
                      "(alter-var-root #'is.simm.partial-cps.ioc/binding-restorers (constantly (delay {})))
                       (alter-var-root #'is.simm.partial-cps.ioc/binding-scopes (constantly (delay {})))
                       (doseq [[_ v] (ns-interns 'is.simm.partial-cps.ioc)] (alter-meta! v assoc :sci/built-in true))")
    (sci/eval-string* ctx "is.simm.partial-cps.ioc/invert")))

(declare expose-effect!)

(defn install!
  "Installs the v2 body surface into the forkable SCI context `ctx` (created
   with `:runtime-mode :forkable`); forks made afterwards share it. Returns
   `ctx`. Options:

   - `:select` – the resolver, see `set-resolver!`.
   - `:effects` – `{sci-sym registered-sym}`, see `expose-effect!`.
   - `:old-names` – nil (default), `:task` or `:spin`: also install
     `org.replikativ.spindel.spin.cps/spin` as v2 `task` (one-shot, started
     at once) or as v2 `spin` (a cached, lazy computation), and
     `org.replikativ.spindel.effects.await/await` as `await`.

   Code then acts in the world the host binds (`v2/*world*`) or, inside a
   body, in the world of the slice."
  ([ctx] (install! ctx {}))
  ([ctx {:keys [select effects] old :old-names}]
   (lineage ctx)
   (when (::config @(:env ctx))
     (throw (ex-info "v2.sci is already installed in this SCI context" {:type ::installed})))
   (when-not (contains? #{nil :task :spin} old)
     (throw (ex-info ":old-names is nil, :task or :spin" {:type ::invalid-options})))
   (let [cfg (atom {:select select :effects {}})
         a (abi cfg ctx)
         ms (macros cfg a)]
     (swap! cfg assoc :abi a)
     (swap! (:env ctx) assoc ::config cfg)
     (doseq [[n c] {'java.lang.Throwable Throwable 'is.simm.partial-cps.ioc/Throwable Throwable}]
       (sci/add-class! ctx n c))
     ;; ioc's output calls these by name; nothing else of the runtime
     (let [n* (sci/create-ns 'is.simm.partial-cps.runtime)]
       (sci/add-namespace! ctx 'is.simm.partial-cps.runtime
                           (into {} (map (fn [[n f]] [n (sci/new-var n f (read-only n*))]))
                                 {'->thunk pr/->thunk 'thunk? pr/thunk? 'force-thunk pr/force-thunk
                                  'scope-continuation pr/scope-continuation})))
     (swap! cfg assoc
            :invert (load-ioc! ctx)
            :bp (with-meta (bp cfg a) {:is.simm.partial-cps.ioc/eager-arguments true}))
     (let [n* (sci/create-ns core-ns)]
       (sci/add-namespace! ctx core-ns
                           (merge (into {} (map (fn [[n f]] [n (sci/new-macro-var n f (read-only n*))])) ms)
                                  (into {} (map (fn [n] [n (sci/new-var n (outside n) (read-only n*))]))
                                        (keys builtin-effects)))))
     (when old
       (let [resolve-core #(sci/eval-string* ctx (str "(var " core-ns "/" % ")"))]
         (sci/add-namespace! ctx 'org.replikativ.spindel.spin.cps
                             {'spin (resolve-core (if (= old :task) "task" "spin"))})
         (sci/add-namespace! ctx 'org.replikativ.spindel.effects.await
                             {'await (resolve-core "await")})))
     (swap! cfg assoc :protected
            (cond-> #{core-ns 'is.simm.partial-cps.ioc 'is.simm.partial-cps.runtime}
              old (into ['org.replikativ.spindel.spin.cps 'org.replikativ.spindel.effects.await])))
     (guard-mappings! ctx cfg)
     (doseq [[s h] effects] (expose-effect! ctx s h))
     ctx)))

(defn expose-effect!
  "Makes the effect the host registered as `registered-sym`
   (`v2/register-effect!`, `v2/defeffect`) callable from SCI bodies as
   `sci-sym` (qualified). Bodies compiled before do not see it (R3).
   Effects are data: a library that registers effects (foerster) can export
   the map `{sci-sym registered-sym}` for the host to pass to `install!`."
  [ctx sci-sym registered-sym]
  (when-not (and (qualified-symbol? sci-sym) (qualified-symbol? registered-sym)
                 (not= (str core-ns) (namespace sci-sym)))
    (throw (ex-info "effects are named by qualified symbols, outside v2.core"
                    {:type ::invalid-options :effect sci-sym})))
  (let [cfg (config ctx)
        n (symbol (name sci-sym))
        ns-sym (symbol (namespace sci-sym))]
    (sci/add-namespace! ctx ns-sym {n (sci/new-var n (outside n) (read-only (sci/create-ns ns-sym)))})
    (swap! cfg update :protected conj sci-sym)
    (swap! cfg assoc-in [:effects sci-sym] ((:custom (:abi @cfg)) registered-sym))
    nil))

(defn set-resolver!
  "Configures which interpreter SCI code of `ctx`'s lineage runs in when a
   body starts or resumes: `(select world interpreter)` is called inside the
   slice with the world being processed and the interpreter the code was
   captured in, and returns an interpreter of the same lineage (`sci/fork`s
   of one context); nil to refuse (the run fails without running SCI code
   and its finalizers are dropped); or a pending value (promise, future) of
   an interpreter it prepares off the slice, e.g. a lazy `sci/fork`: the run
   parks until it is realized and asks again. It runs under the world's gate
   and must not wait (B7): no `sci/fork` inside it. nil removes the
   resolver: code runs where it was captured."
  [ctx select]
  (swap! (config ctx) assoc :select select)
  nil)

(defn eval-string
  "Evaluates `source` in `ctx` with `v2/*world*` bound to `world` (host:
   top-level work, e.g. an offloaded evaluation)."
  [world ctx source]
  (binding [v2/*world* world]
    (sci/eval-string* ctx source)))
