(ns org.replikativ.spindel.log
  "Lightweight logging helpers for Spindel built on Trove.

  - Configure once via `configure!` (default: console backend)
  - Use structured logging everywhere via `debug!`, `info!`, etc.

  Trove’s log! macro requires a compile-time map literal. You can include
  symbols inside the map (e.g. `{:data {:spin-id spin-id}}`), but the outer
  form must be a literal map.
  "
  (:require
   [taoensso.trove :as trove]
   [taoensso.trove.console :as trove.console])
  #?(:cljs (:require-macros [org.replikativ.spindel.log])))

(defn configure!
  "Configure Trove backend.

  Options:
  - :backend   One of #{:console} (more can be added later). Defaults to :console.
  - :min-level One of #{nil :trace :debug :info :warn :error :fatal :report}.
               When set, logs below this level will noop. Defaults to :info (JVM), nil (JS)."
  ([] (configure! nil))
  ([{:keys [backend min-level]}]
   (let [backend (or backend :console)
         get-fn  (case backend
                   :console trove.console/get-log-fn
                   ;; Future: :timbre, :telemere, etc.
                   trove.console/get-log-fn)
         lf      (get-fn (cond-> {}
                            min-level (assoc :min-level min-level)))]
     (trove/set-log-fn! lf))))

#?(:clj
   (defmacro log!
     "Generic wrapper if you want to pass :level explicitly.
     Prefer the level-specific helpers below for convenience."
     [opts]
     `(trove/log! ~opts)))

#?(:clj (defmacro trace!  [opts] `(trove/log! ~(assoc opts :level :trace))))
#?(:clj (defmacro debug!  [opts] `(trove/log! ~(assoc opts :level :debug))))
#?(:clj (defmacro info!   [opts] `(trove/log! ~(assoc opts :level :info))))
#?(:clj (defmacro warn!   [opts] `(trove/log! ~(assoc opts :level :warn))))
#?(:clj (defmacro error!  [opts] `(trove/log! ~(assoc opts :level :error))))
#?(:clj (defmacro fatal!  [opts] `(trove/log! ~(assoc opts :level :fatal))))
#?(:clj (defmacro report! [opts] `(trove/log! ~(assoc opts :level :report))))
