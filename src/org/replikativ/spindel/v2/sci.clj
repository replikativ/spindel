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
   handler is a value, not a name, and the installed namespaces (and those of
   exposed effects) are read-only namespaces (`read-only-ns`): no new names,
   `ns-unmap`, `remove-ns` or `require :reload`.

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

   **Budget (B3 exception, spec Z#80).** An elapsed-time limit checked at
   polls, off by default (`install!`'s `:slice-budget-ms`): the first poll
   past it aborts, also code that would have terminated. The unit is an adapter
   activation: the outermost entry of a run's code on a thread, including
   continuations of the run resumed synchronously on that stack; a nested
   activation of another run (a computation demanded on the stack) has its
   own clock and pauses the parent's. The embedding's `:interrupt-fn` calls
   `check-budget!`; past the budget it throws SCI's uncatchable interrupt,
   so no catch (user or generated) handles it and SCI native `finally`
   blocks are attempted. At the activation's `in-run` the abort becomes:
   - the run's open finally regions closed innermost first in the model's
     order (an open region exits and leaves, a running clause leaves), so the
     run retires and its world completes;
   - an ordinary error `{:type ::budget-exceeded :hard true}` without a
     cause, through the normal error path (T12): creditors catch it like any
     error and never see the interrupt; a run already cancelled stays
     cancelled;
   - no SCI code of the run afterwards: its error continuation passes the
     error on, effects, creations, scopes, paths and completions of the
     aborted activation throw the interrupt again, and continuations
     captured in it never enter SCI (a run it left parked fails when it
     resumes; an external whose start callback was aborted fails at once);
   - `:on-abandon` once, off the gate.
   This breaks B3 for the aborted activation: finalizers not yet run are
   skipped or truncated, effects already performed persist, and a resource
   a skipped finalizer would have returned (a semaphore permit) stays taken
   until its owner scope closes. Allocation is not bounded here.

   **No waiting in a slice (B7).** SCI evaluation holds no lock that a fork
   or retirement waits for (replikativ SCI >= 0.15.59-replikativ.9), so a
   slice enters the interpreter directly, and a resolver may `sci/fork`
   lazily inside the slice."
  (:require [clojure.java.io :as io]
            [is.simm.partial-cps.runtime :as pr]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [sci.core :as sci]
            [sci.ctx-store :as store]
            [sci.interrupt :as interrupt]))

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

;; The adapter activation running on this thread: the outermost `in-run`
;; entry of a run in a world, an array [world run regions deadline budget
;; aborted? dead]. `regions` holds the run's finally stack as SCI code
;; changed it through the spliced functions, innermost last: `:open` (a
;; region whose body runs, the engine's R-FINS) or `:running` (its finally
;; clause runs, R-INFIN). `deadline` and `budget` are nanos (nil: no
;; budget). `dead` is a cell the continuations captured in the activation
;; share: set when it is hard-aborted (`dead-here`).
(def ^:private ^ThreadLocal adapting (ThreadLocal.))

(defn- activation
  "The activation of the run on this thread, when the adapter runs it."
  ^objects []
  (when-let [^objects a (.get adapting)]
    (when (and (identical? (aget a 0) (v2/cw)) (identical? (aget a 1) (v2/active-run)))
      a)))

(defn- regions
  "The finally stack holder of the run on this thread, when the adapter
   runs it."
  ^objects []
  (when-let [a (activation)] (aget a 2)))

(defn- close-regions!
  "Closes the run's open regions, whose SCI code cannot run (refusal, hard
   abort) or which SCI code left open (completion), so the run can retire.
   Innermost first, each in the model's order: an open region exits, then
   leaves; a running clause leaves. Returns how many were closed."
  [^objects b]
  (loop [st (aget b 0) n 0]
    (if-let [top (peek st)]
      (do (when (= :open top) (v2/exit-finally!))
          (v2/leave-finalizer!)
          (aset b 0 (pop st))
          (recur (pop st) (inc n)))
      n)))

(defn- abort-again!
  "Continues a hard abort: SCI's uncatchable interrupt, so no interpreted
   catch (user or generated) handles it on its way to the activation's
   `in-run`."
  []
  (interrupt/interrupt! "SCI slice budget exceeded" {::budget true}))

(defn- live!
  "Nothing of an aborted activation runs on: no effect, creation, scope,
   path or completion (B1: its slice can then only throw). The finally
   bookkeeping and closing a scope or path stay allowed: they are unwind."
  []
  (when-let [a (activation)] (when (aget a 5) (abort-again!))))

(defn- dead-here
  "The budget error when `cell` (of the activation a continuation was
   captured in) records a hard abort that applies to the world processed
   now: the aborted world itself, or a world forked from it after the abort
   (its fork cut is not below the id counter at the abort). Savepoint
   instances and forks made before keep their own runs."
  [^objects cell]
  (when cell
    (when-let [[e wid fam next-id] (aget cell 0)]
      (let [w (v2/cw)]
        (when (and w (identical? (hs/deref-weak fam) (rw/g w rw/W-FAMILY))
                   (or (= wid (rw/g w rw/ID))
                       (some (fn [[a cut]] (and (= a wid) (>= (long cut) (long next-id))))
                             (rw/g w rw/W-LINEAGE))))
          e)))))

(defn check-budget!
  "The budget poll (`:slice-budget-ms`, see `install!`). The embedding calls
   it from the SCI context's `:interrupt-fn`, which SCI calls at every
   interpreted fn and loop entry. When the activation running on this
   thread is past its budget, it is aborted with SCI's uncatchable interrupt
   (`sci.interrupt/interrupt!`); code that keeps running after the abort (a
   native `finally` that loops, or a host helper that swallowed the
   interrupt) is interrupted again after another budget. Outside an
   activation it does nothing."
  []
  (when-let [^objects a (.get adapting)]
    (when-let [dl (aget a 3)]
      (let [now (System/nanoTime)]
        (when (and (> (- now (long dl)) 0)
                   (identical? (aget a 0) (v2/cw)) (identical? (aget a 1) (v2/active-run)))
          (aset a 5 true)
          (aset a 3 (num (+ now (long (aget a 4)))))
          (abort-again!)))))
  nil)

(defn- capture
  "[interpreter continuation-context regions] of the SCI code running now.
   The interpreter is SCI's current context when it belongs to `home`'s
   lineage, else `home` (a host thread calling an SCI function). A body
   (`body? true`) starts with no open region; a continuation with the run's
   finally stack (an immutable snapshot: savepoint instances share it)."
  [home body?]
  (live!)
  (let [cur store/*ctx*
        ctx (if (and cur (identical? (:sci.impl/lineage cur) (:sci.impl/lineage home))) cur home)
        a (when-not body? (activation))]
    [ctx (sci/capture-continuation-context ctx) (if a (aget ^objects (aget a 2) 0) []) (when a (aget a 6))]))

(defn- select
  "The interpreter to run captured code of `ctx` in, for world `w`."
  [cfg w ctx]
  (if-let [f (:select @cfg)]
    (or (f w ctx)
        (throw (ex-info "no SCI interpreter for this world" {:type ::no-interpreter})))
    ctx))

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

;; [world run error] while a run's continuation hands its own failure (a
;; refusal or a hard abort) to its error continuation: set when `k` leaves
;; with it, taken by the next error continuation entered on the thread,
;; which the engine calls at once (resume-k)
(def ^:private ^ThreadLocal handing-off (ThreadLocal.))

(defn- refuse!
  "The run's SCI code cannot run here: its open regions are dropped (their
   finalizers are SCI code) and the slice fails, so the run fails and
   retires without running SCI code. Returns the error to throw."
  [b t]
  (close-regions! b)
  (if (= ::no-interpreter (:type (ex-data t)))
    t
    (ex-info "no SCI interpreter for this world" {:type ::no-interpreter} t)))

(defn- handed-off?
  "Whether `e` is the run's own failure its continuation just handed on
   (not another run's error this run awaited, which its code may catch).
   Takes the record."
  [e]
  (when-let [^objects a (.get handing-off)]
    (.remove handing-off)
    (and (identical? e (aget a 2))
         (identical? (aget a 0) (v2/cw)) (identical? (aget a 1) (v2/active-run)))))

(defn- budget-ex
  "The error a hard-aborted run completes with: ordinary, with no cause (the
   SCI interrupt never reaches a creditor)."
  [budget-nanos]
  (ex-info "SCI slice budget exceeded"
           {:type ::budget-exceeded :hard true :budget-ms (quot (long budget-nanos) 1000000)}))

(defn- notify-abandon!
  "Delivers `:on-abandon` once, off the gate; its throw is reported and
   changes nothing."
  [cfg report]
  (when-let [f (:on-abandon @cfg)]
    (hs/execute-surely! (hs/executor)
                        (fn [] (try (f report)
                                    (catch Throwable t
                                      (binding [*out* *err*] (println "v2.sci :on-abandon failed:" t))))))))

(defn- abandon!
  "The hard path: the aborted activation's open regions are closed in the
   model's order (their remaining finalizers are skipped, a B3 exception)
   and the run fails with the budget error. Its continuations are dead from
   now on (`dead-here`): a run the activation left parked (an external
   whose start callback was aborted) never re-enters SCI and fails when it
   resumes. Returns the error to throw."
  [cfg ^objects a]
  (let [w (aget a 0) r (aget a 1)
        e (budget-ex (aget a 4))]
    (aset ^objects (aget a 6) 0
          [e (rw/g w rw/ID) (hs/weak (rw/g w rw/W-FAMILY))
           (let [^java.util.concurrent.atomic.AtomicLong n (rw/g w rw/W-NEXT)] (.get n))])
    (let [n (close-regions! (aget a 2))]
      (notify-abandon! cfg {:world w :run-id (rw/g r rw/ID) :regions n
                            :budget-ms (quot (long (aget a 4)) 1000000)}))
    e))

(defn- thunk-or-nil
  "What an effect returns to the body: a Thunk of its own code, else nothing."
  [x]
  (when (pr/thunk? x) x))

(defn- in-run*
  "Runs `(f)` as code of the active run: in the interpreter selected for the
   processed world, with the SCI bindings and finally stack of `cap`,
   forcing its Thunks. Entering the interpreter waits for nothing: SCI
   evaluation holds no lock a fork or retirement waits for.

   An outermost entry is an activation, with its own budget clock; a nested
   activation of another run pauses it. A hard-aborted activation leaves
   with the budget error (`abandon!`), a refused one with the refusal; both
   are put in `own` when given (a continuation hands them on)."
  [cfg [ctx cc stack] f ^objects own]
  (let [w (v2/cw)
        r (v2/active-run)
        ^objects prev (.get adapting)]
    (if (and r prev (identical? w (aget prev 0)) (identical? r (aget prev 1)))
      (do (when (aget prev 5) (abort-again!)) (f))
      (let [b (doto (object-array 1) (aset 0 stack))
            budget (when-let [ms (:slice-budget-ms @cfg)] (* 1000000 (long ms)))
            t0 (System/nanoTime)
            a (doto (object-array 7)
                (aset 0 w) (aset 1 r) (aset 2 b)
                (aset 3 (when budget (+ t0 (long budget)))) (aset 4 budget) (aset 5 false)
                (aset 6 (object-array 1)))
            entered (volatile! false)
            fail (fn [e] (when own (aset own 0 e)) (throw e))]
        (.set adapting a)
        (try
          (let [v (try
                    (let [target (select cfg w ctx)
                          run (sci/continuation-context-fn (sci/retarget-continuation-context cc target)
                                                           (fn [] (vreset! entered true) (force-all (f))))]
                      (run))
                    (catch Throwable t
                      (cond (aget a 5) a          ; aborted: abandoned below
                            @entered (throw (unwrap t))
                            :else (fail (refuse! b t)))))]
            ;; also when a host helper swallowed the abort and the code returned
            (if (aget a 5) (fail (abandon! cfg a)) v))
          (finally
            (.set adapting prev)
            ;; the parent's clock does not run while a nested activation
            ;; does, its abort translation and region closing included
            (when prev
              (when-let [dl (aget prev 3)]
                (aset prev 3 (num (+ (long dl) (- (System/nanoTime) t0))))))))))))

(defn- in-run [cfg cap f] (in-run* cfg cap f nil))

(defn- settled
  "The engine continuation `k` (a body's ok or err): regions SCI code left
   open are closed first, so the completed run retires."
  [k]
  (fn [v]
    (live!)
    (when-let [b (regions)] (close-regions! b))
    (k v)))

(defn- in-interpreter
  "`f` for a host call outside the slice (offload's f, external's f and
   cancel fn, await-op's op). When it is called, the resolver selects the
   interpreter, as for a slice, for the world being processed then, else the
   world of the effect (`w`, an executor thread processes none); `f` runs
   there with the SCI bindings of `cap`. When the interpreter is refused
   (resolver nil, or it cannot be entered: another lineage, retired) no SCI
   code runs and the call returns `(refused e)`."
  [cfg w [ctx cc] f refused]
  (fn [& args]
    (let [entered (volatile! false)]
      (try (let [target (select cfg (or (v2/cw) w) ctx)]
             ((sci/continuation-context-fn (sci/retarget-continuation-context cc target)
                                           (fn [] (vreset! entered true) (apply f args)))))
           (catch Throwable t
             (if @entered
               ;; called in an aborted activation (e.g. an external's f in
               ;; the slice): what an engine catch may keep is ordinary
               (throw (let [a (activation)] (if (and a (aget a 5)) (budget-ex (aget a 4)) (unwrap t))))
               (refused (if (= ::no-interpreter (:type (ex-data t)))
                          t
                          (ex-info "no SCI interpreter for this world" {:type ::no-interpreter} t)))))))))

(defn- fail-refused
  "A refused offload f, external f or await-op op fails its effect."
  [e]
  (throw e))

(defn- join-refused
  "A refused external cancel fn counts as joined: none of the operation's
   SCI code can run any more (its host-side work may continue)."
  [_]
  :joined)

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
  (let [err* (fn [cap ek] (fn [e]
                            (cond
                              (handed-off? e) (throw e)   ; to the slice: the run fails without SCI code
                              :else (if-let [x (dead-here (nth cap 3))]
                                      (throw x)           ; captured in a hard-aborted activation
                                      (in-run cfg cap #(ek e))))))
        ;; the engine routes a throw of `k` to `ek` (resume-k): the run's own
        ;; failure is recorded for exactly that handoff
        k* (fn [cap k] (fn [v]
                         (when-let [x (dead-here (nth cap 3))] (throw x))
                         (let [own (object-array 1)]
                           (try (in-run* cfg cap #(k v) own)
                                (catch Throwable t
                                  (when (identical? t (aget own 0))
                                    (.set handing-off (doto (object-array 3)
                                                        (aset 0 (v2/cw)) (aset 1 (v2/active-run)) (aset 2 t))))
                                  (throw t))))))
        body* (fn [cap body] (fn [ok err] (in-run cfg cap #(body (settled ok) (settled err)))))
        fx (fn [native]
             (fn [x k ek]
               (let [cap (capture home false)]
                 (thunk-or-nil (native x (k* cap k) (err* cap ek))))))]
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
                  (thunk-or-nil (v2/offload-effect! (in-interpreter cfg (v2/cw) cap f fail-refused) opts
                                                    (k* cap k) (err* cap ek)))))
     :external (fn [f k ek]
                 (let [cap (capture home false)
                       w (v2/cw)]
                   (thunk-or-nil (v2/external-effect! (fn [complete!]
                                                        (let [c ((in-interpreter cfg w cap f fail-refused) complete!)]
                                                          ;; aborted in the start callback (a host helper
                                                          ;; swallowed it): the effect fails now, so the
                                                          ;; parked run resumes into its failure
                                                          (when-let [^objects a (activation)]
                                                            (when (aget a 5) (throw (budget-ex (aget a 4)))))
                                                          (if (fn? c) (in-interpreter cfg w cap c join-refused) c)))
                                                      (k* cap k) (err* cap ek)))))
     :await-op (fn [op opts k ek]
                 (let [cap (capture home false)]
                   (thunk-or-nil (v2/await-op-effect! (in-interpreter cfg (v2/cw) cap op fail-refused) opts
                                                      (k* cap k) (err* cap ek)))))
     :savepoint (fn [site payload k ek]
                  (let [cap (capture home false)]
                    (thunk-or-nil (v2/savepoint-effect! site payload (k* cap k) (err* cap ek)))))
     :custom (fn [sym]
               (fn [args site k ek]
                 (let [cap (capture home false)]
                   (thunk-or-nil (v2/custom-effect! sym args site (k* cap k) (err* cap ek))))))
     ;; balanced only: a region opens in a run the adapter runs; the
     ;; innermost open region exits, the innermost running clause leaves
     ;; (B3; unbalanced calls change nothing)
     :enter-finally (fn [] (when-let [b (regions)] (v2/enter-finally!) (aset b 0 (conj (aget b 0) :open))) nil)
     :exit-finally (fn [] (when-let [b (regions)]
                            (let [st (aget b 0)]
                              (when (= :open (peek st))
                                (v2/exit-finally!) (aset b 0 (conj (pop st) :running)))))
                     nil)
     :leave-finalizer (fn [] (when-let [b (regions)]
                               (let [st (aget b 0)]
                                 (when (= :running (peek st))
                                   (v2/leave-finalizer!) (aset b 0 (pop st)))))
                        nil)
     ;; a scope or saved path acts only in the run that opened it (refused,
     ;; with no effect, in another run or an unrelated world)
     :open-scope (fn [] (live!) (opened (v2/open-scope!)))
     :close-scope (fn [s] (when-let [x (own s identity)] (v2/close-scope-fx! x)) nil)
     :push-path (fn [p] (live!) (opened (v2/push-path! p)))
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

(defn- read-only
  "Var metadata SCI refuses to redefine, `alter-var-root` or `alter-meta!`
   (`:sci/built-in`): code in the interpreter cannot change how later bodies
   compile."
  [ns-obj]
  {:ns ns-obj :sci/built-in true})

(defn- read-only-ns
  "A namespace object for `ns-sym` that SCI keeps read-only to interpreted
   code (`:sci/built-in` on the namespace, SCI >= 0.15.59-replikativ.9): no
   new names (`def`, `intern`, types), no `ns-unmap`, `remove-ns` or
   `require :reload`. Keeps the metadata of the existing one."
  [ctx ns-sym]
  (sci/create-ns ns-sym (assoc (meta (get-in @(:env ctx) [:namespaces ns-sym :obj])) :sci/built-in true)))

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
    (sci/add-namespace! ctx 'is.simm.partial-cps.ioc {:obj (read-only-ns ctx 'is.simm.partial-cps.ioc)})
    (sci/eval-string* ctx "is.simm.partial-cps.ioc/invert")))

(declare expose-effect!)

(defn install!
  "Installs the v2 body surface into the forkable SCI context `ctx` (created
   with `:runtime-mode :forkable`); forks made afterwards share it. Returns
   `ctx`. Options:

   - `:select` – the resolver, see `set-resolver!`.
   - `:effects` – `{sci-sym registered-sym}`, see `expose-effect!`.
   - `:slice-budget-ms` – nil (default: off) or the elapsed-time budget of
     one adapter activation, checked at polls (see the namespace
     doc, Budget). It needs `ctx` to have an `:interrupt-fn` that calls
     `check-budget!`.
   - `:on-abandon` – called once, off the gate, with `{:world :run-id
     :regions :budget-ms}` when an activation is hard-aborted (`:regions`:
     how many open finally regions were closed without their finalizers).
   - `:old-names` – nil (default), `:task` or `:spin`: also install
     `org.replikativ.spindel.spin.cps/spin` as v2 `task` (one-shot, started
     at once) or as v2 `spin` (a cached, lazy computation), and
     `org.replikativ.spindel.effects.await/await` as `await`.

   Code then acts in the world the host binds (`v2/*world*`) or, inside a
   body, in the world of the slice."
  ([ctx] (install! ctx {}))
  ([ctx {:keys [select effects slice-budget-ms on-abandon] old :old-names}]
   (lineage ctx)
   (when (::config @(:env ctx))
     (throw (ex-info "v2.sci is already installed in this SCI context" {:type ::installed})))
   (when-not (contains? #{nil :task :spin} old)
     (throw (ex-info ":old-names is nil, :task or :spin" {:type ::invalid-options})))
   (when-not (or (nil? slice-budget-ms) (pos-int? slice-budget-ms))
     (throw (ex-info ":slice-budget-ms is nil or a positive integer" {:type ::invalid-options})))
   (when (and slice-budget-ms (nil? (:interrupt-fn ctx)))
     (throw (ex-info ":slice-budget-ms needs an :interrupt-fn in the SCI context that calls check-budget!"
                     {:type ::invalid-options})))
   (when-not (or (nil? on-abandon) (ifn? on-abandon))
     (throw (ex-info ":on-abandon is nil or a function" {:type ::invalid-options})))
   (let [cfg (atom {:select select :effects {} :slice-budget-ms slice-budget-ms :on-abandon on-abandon})
         a (abi cfg ctx)
         ms (macros cfg a)]
     (swap! cfg assoc :abi a)
     (swap! (:env ctx) assoc ::config cfg)
     (doseq [[n c] {'java.lang.Throwable Throwable 'is.simm.partial-cps.ioc/Throwable Throwable}]
       (sci/add-class! ctx n c))
     ;; ioc's output calls these by name; nothing else of the runtime
     (let [n* (read-only-ns ctx 'is.simm.partial-cps.runtime)]
       (sci/add-namespace! ctx 'is.simm.partial-cps.runtime
                           (into {:obj n*}
                                 (map (fn [[n f]] [n (sci/new-var n f (read-only n*))]))
                                 {'->thunk pr/->thunk 'thunk? pr/thunk? 'force-thunk pr/force-thunk
                                  'scope-continuation pr/scope-continuation})))
     (swap! cfg assoc
            :invert (load-ioc! ctx)
            :bp (with-meta (bp cfg a) {:is.simm.partial-cps.ioc/eager-arguments true}))
     (let [n* (read-only-ns ctx core-ns)]
       (sci/add-namespace! ctx core-ns
                           (merge {:obj n*}
                                  (into {} (map (fn [[n f]] [n (sci/new-macro-var n f (read-only n*))])) ms)
                                  (into {} (map (fn [n] [n (sci/new-var n (outside n) (read-only n*))]))
                                        (keys builtin-effects)))))
     (when old
       (let [resolve-core #(sci/eval-string* ctx (str "(var " core-ns "/" % ")"))]
         (sci/add-namespace! ctx 'org.replikativ.spindel.spin.cps
                             {:obj (read-only-ns ctx 'org.replikativ.spindel.spin.cps)
                              'spin (resolve-core (if (= old :task) "task" "spin"))})
         (sci/add-namespace! ctx 'org.replikativ.spindel.effects.await
                             {:obj (read-only-ns ctx 'org.replikativ.spindel.effects.await)
                              'await (resolve-core "await")})))
     (doseq [[s h] effects] (expose-effect! ctx s h))
     ctx)))

(defn expose-effect!
  "Makes the effect the host registered as `registered-sym`
   (`v2/register-effect!`, `v2/defeffect`) callable from SCI bodies as
   `sci-sym` (qualified). Bodies compiled before do not see it (R3).

   The namespace of `sci-sym` becomes a read-only SCI namespace: from then
   on interpreted code, `sci/intern` and `require :reload` cannot add,
   remove or reload names in it; only the host's `sci/add-namespace!` can
   extend it. So expose effects from a dedicated effects namespace, or from
   a namespace whose SCI-side code is loaded first. (Without this, code could
   unmap the effect for everyone, or redefine its name as a macro that later
   bodies, any agent's, would expand in place of the effect.)
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
    ;; the effect's namespace becomes read-only to interpreted code (the host
    ;; may still add to it): a stub removed or replaced would change what
    ;; later code names
    (let [n* (read-only-ns ctx ns-sym)]
      (sci/add-namespace! ctx ns-sym {:obj n* n (sci/new-var n (outside n) (read-only n*))}))
    (swap! cfg assoc-in [:effects sci-sym] ((:custom (:abi @cfg)) registered-sym))
    nil))

(defn set-resolver!
  "Configures which interpreter SCI code of `ctx`'s lineage runs in when a
   body starts or resumes: `(select world interpreter)` is called inside the
   slice with the world being processed and the interpreter the code was
   captured in, and returns an interpreter of the same lineage (`sci/fork`s
   of one context), or nil to refuse (the run fails without running SCI
   code and its finalizers are dropped). It runs under the world's gate and
   must not wait (B7); `sci/fork` does not wait (SCI >= 0.15.59-replikativ.9),
   so it may fork an interpreter lazily, also while an evaluation of the
   source is running. nil removes the resolver: code runs where it was
   captured."
  [ctx select]
  (swap! (config ctx) assoc :select select)
  nil)

(defn eval-string
  "Evaluates `source` in `ctx` with `v2/*world*` bound to `world` (host:
   top-level work, e.g. an offloaded evaluation)."
  [world ctx source]
  (binding [v2/*world* world]
    (sci/eval-string* ctx source)))
