(ns org.replikativ.spindel.engine.fault
  "Engine-wide fault reporting hook.

  spindel carries no logging dependency, but an engine fault — a
  continuation that throws during resume, an executor task whose
  exception would otherwise vanish into a discarded Future, a consumer
  fault isolated away from a producer — must never be silently
  swallowed. This namespace is the single, dependency-free hook every
  engine path reports through; embedders route it into their own
  logging (simmis → Telemere) via `set-fault-reporter!`.

  Hoisted from `pubsub/mult.cljc` (PR #28 introduced the pattern there
  for `::watcher-fault` / `::pump-rejected`); mult now delegates here so
  one embedder call configures ALL engine fault reporting.

  Event keywords currently reported through this hook:

    :org.replikativ.spindel.engine.fault/continuation-fault
      A resumed waiter/reader/parent continuation threw. Data:
      {:site :mailbox|:deferred|:spin-completion|:cont-resume
       :spin-id …, :error e}. The owning spin is rejected (loud
      failure, at-most-once delivery — see engine.md §Threading
      contract); this report is the observability side.

    :org.replikativ.spindel.engine.fault/executor-task-fault
      A task submitted to an executor threw and nothing upstream could
      observe it (the JVM `.submit` Future is discarded; a CLJS
      setTimeout callback has no caller). Data: {:error e}.

    :org.replikativ.spindel.pubsub.mult/watcher-fault
    :org.replikativ.spindel.pubsub.mult/pump-rejected
      See pubsub/mult.cljc."
  #?(:clj (:import [java.io Writer])))

(defonce ^:private fault-reporter
  ;; Default: stderr / console.error so a fault is never silently
  ;; swallowed even in an unconfigured embedding.
  (atom (fn [event data]
          #?(:clj  (binding [*out* *err*]
                     (println "[spindel.fault]" event (pr-str data)))
             :cljs (js/console.error "[spindel.fault]" (str event) (clj->js data))))))

(defn set-fault-reporter!
  "Override how the engine reports faults. `f` is
  (fn [event-keyword data-map]). Default writes to stderr /
  console.error. One hook covers the whole engine — continuation
  faults, executor task faults, and the pubsub events that previously
  had their own reporter in `pubsub/mult.cljc`."
  [f] (reset! fault-reporter f))

(defn ^:no-doc current-fault-reporter
  "The currently installed reporter fn. For save/restore around a
  scoped override (tests, temporarily-quiet sections)."
  []
  @fault-reporter)

(defn report-fault!
  "Report an engine fault through the configured reporter. Never throws:
  a broken reporter must not take down the path that is trying to be
  loud about a fault."
  [event data]
  (try (@fault-reporter event data)
       (catch #?(:clj Throwable :cljs :default) _ nil)))
