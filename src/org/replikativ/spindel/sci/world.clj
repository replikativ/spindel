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
  ComponentRef; resolving it in a descendant selects the forked interpreter."
  ([runtime]
   (create! runtime {}))
  ([runtime opts]
   (let [ref-holder (volatile! nil)
         interpreter
         (binding [ec/*execution-context* runtime]
           (sci/with-detached-context
             #(macro/create-spin-macro-context
               (assoc opts
                      :runtime runtime
                      :resolve-sci-context
                      (fn [execution-context]
                        (context-in execution-context @ref-holder))))))
         ref (binding [ec/*execution-context* runtime]
               (component/register! (->InterpreterWorld interpreter)))]
     (vreset! ref-holder ref)
     ref)))

(defn eval-string*
  "Evaluate `source` in interpreter `ref` selected by the current world."
  [ref source]
  (sci/eval-string* (context ref) source))
