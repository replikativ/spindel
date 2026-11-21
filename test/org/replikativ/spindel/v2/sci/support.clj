(ns org.replikativ.spindel.v2.sci.support
  "Shared setup for the v2.sci tests: verify worlds, installed interpreters."
  (:require [clojure.test :refer [is]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.sci :as v2sci]
            [org.replikativ.spindel.v2.verify :as verify]
            [sci.core :as sci]))

(def ^:dynamic *divergences* nil)

(defn vworld [] (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn interpreter
  "A forkable SCI context, interop locked (no `:allow :all`), with v2.sci
   installed. `sci-opts` go to `sci/init`, `opts` to `install!`."
  ([] (interpreter {} {}))
  ([sci-opts] (interpreter sci-opts {}))
  ([sci-opts opts]
   (v2sci/install! (sci/init (assoc sci-opts :runtime-mode :forkable)) opts)))

(def prelude
  "(require '[org.replikativ.spindel.v2.core :refer [spin task task-with aseq await track sleep
                                                    with-scope with-path offload external await-op
                                                    await-all await-any take! savepoint]]) ")

(defn ev
  "Evaluates `source` (after the prelude) in `ctx`, in world `w`."
  [w ctx source]
  (v2sci/eval-string w ctx (str prelude source)))

(defn v [h] (v2/value h 2000 ::timeout))

(defn outcome
  "The value of `h`, or [:failed data] when it fails."
  [h]
  (try (v2/value h 2000 ::timeout)
       (catch clojure.lang.ExceptionInfo e [:failed (ex-data e)])))

(defn wait-until [f]
  (loop [n 0] (cond (f) true (> n 400) false :else (do (Thread/sleep 5) (recur (inc n))))))
