(ns org.replikativ.spindel.sci.world
  "SCI interpreters as ordinary fork-selected Spindel world components."
  (:require [sci.core :as sci]
            [org.replikativ.spindel.engine.component :as component]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.sci.macro :as macro]))

(defrecord InterpreterWorld [context]
  component/PWorldComponent
  (realization [this] this)

  component/PComponentRetirement
  (retire-component! [_]
    (sci/retire! context))

  component/PComponentForkRecovery
  (failed-fork-cleanup [_ error]
    (when (sci/fork-recovery? error)
      ;; This receipt is HOST construction state, never a world component.
      (let [latest (volatile! error)]
        (reify component/PComponentRetirement
          (retire-component! [_]
            (try (sci/recover-fork! @latest)
                 (catch Throwable failure
                   (vreset! latest failure)
                   (throw failure))))))))

  rtp/PForkable
  (fork-value [_ _fork-id _directive]
    (->InterpreterWorld (sci/fork context))))

(defn context-in
  "Resolve interpreter `ref` in the explicit Spindel execution context."
  [execution-context ref]
  (:context (component/resolve-in execution-context ref)))

(defn context
  "Resolve interpreter `ref` in the currently bound execution context."
  [ref]
  (:context (component/resolve ref)))

(defn retire-in!
  "Release the exact interpreter owned in `runtime`, then remove its lookup.

   HOST-only: the caller must fence new use/publication and join actual work,
   including callbacks and parked computations, before calling. Snapshot
   quiescence or stopping the drain does not supply that lifetime fence.
   Do not call on the drain or inside a backend updater.

   `expected` must be identical to the selected SCI context. A failed retirement
   retains that selection for retry. Missing entries refuse: lookup absence
   is not a cleanup acknowledgment. Old contexts retained across replacement
   remain owned by the caller; this only releases the selected context.
   Related worlds and deliberately shared components are unaffected."
  [runtime ref expected]
  (when-not (component/component-ref? ref)
    (throw (ex-info "Expected an interpreter component ref"
                    {:type ::invalid-retirement})))
  (let [id (:id ref)
        selected (get (ec/get-state-in runtime [:world/components]) id)]
    (when-not (instance? InterpreterWorld selected)
      (throw (ex-info "Component is not an SCI interpreter in this world"
                      {:type ::not-interpreter :component/id id})))
    (when-not (identical? expected (:context selected))
      (throw (ex-info "SCI interpreter changed before retirement"
                      {:type ::stale-context :component/id id})))
    ;; SCI cleanup can block/throw: never run it inside a retried updater.
    (component/retire-component! selected)
    (binding [ec/*execution-context* runtime]
      (ec/swap-state!
       []
       (fn [state]
         ;; A stale release must never remove a replacement. This check does
         ;; not replace the caller's admission/publication exclusion.
         (when-not (identical? selected (get-in state [:world/components id]))
           (throw (ex-info "SCI interpreter changed during retirement"
                           {:type ::stale-context :component/id id})))
         (-> state
             (update :world/components dissoc id)
             (update :world/forkable-components disj id))))))
  nil)

(defn replace-context!
  "Atomically replace this world's interpreter under its existing stable ref.

   `expected` must be identical to the currently selected SCI context. Callers
   may prepare `(sci/fork expected)` away from the reactive engine, then publish
   that context without changing the ref captured by SCI's runtime resolvers.
   Missing, foreign-type and stale realizations refuse without mutation.

   This only publishes a process-local heap. The caller owns admission,
   quiescence and cleanup of interpreter-specific native resources; neither
   the previous nor the replacement context is implicitly released."
  [runtime ref expected replacement]
  (when-not (and (component/component-ref? ref)
                 (map? replacement)
                 (instance? clojure.lang.IAtom (:env replacement)))
    (throw (ex-info "Expected a component ref and an SCI context"
                    {:type ::invalid-replacement})))
  (binding [ec/*execution-context* runtime]
    (ec/swap-state!
     [:world/components (:id ref)]
     (fn [selected]
       (when-not (instance? InterpreterWorld selected)
         (throw (ex-info "Component is not an SCI interpreter in this world"
                         {:type ::not-interpreter :component/id (:id ref)})))
       (when-not (identical? expected (:context selected))
         (throw (ex-info "SCI interpreter changed during preparation"
                         {:type ::stale-context :component/id (:id ref)})))
       (->InterpreterWorld replacement))))
  replacement)

(defn create!
  "Create and register a forkable SCI interpreter in `runtime`.

  Options are those accepted by `create-spin-macro-context`, except `:runtime`
  and `:resolve-sci-context`, which this component owns. Returns a stable
  ComponentRef; resolving it in a descendant selects the forked interpreter.

  Set `:spindel-primitives? false` to omit Spindel's namespaces, native spin
  bindings and CPS bootstrap. In that mode only `:sci-opts` and `:interrupt-fn`
  configure the interpreter. Its SCI runtime remains forkable and uses the
  same component ownership. This does not restrict capabilities the host
  explicitly supplies through `:sci-opts`."
  ([runtime]
   (create! runtime {}))
  ([runtime opts]
   (when-not (boolean? (get opts :spindel-primitives? true))
     (throw (ex-info ":spindel-primitives? must be a boolean"
                     {:type ::invalid-options})))
   (let [ref-holder (volatile! nil)
         interpreter
         (binding [ec/*execution-context* runtime]
           (sci/with-detached-context
             #(if (get opts :spindel-primitives? true)
                (macro/create-spin-macro-context
                 (assoc opts
                        :runtime runtime
                        :resolve-sci-context
                        (fn [execution-context]
                          (context-in execution-context @ref-holder))))
                (sci/init
                 (-> (:sci-opts opts)
                     (cond-> (:interrupt-fn opts) (assoc :interrupt-fn (:interrupt-fn opts)))
                     (assoc :runtime-mode :forkable)
                     (update :features (fn [features] (or features #{:clj}))))))))
         ref (binding [ec/*execution-context* runtime]
               (component/register! (->InterpreterWorld interpreter)))]
     (vreset! ref-holder ref)
     ref)))

(defn eval-string*
  "Evaluate `source` in interpreter `ref` selected by the current world."
  [ref source]
  (sci/eval-string* (context ref) source))
