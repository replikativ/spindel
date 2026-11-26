(ns org.replikativ.spindel.v2.dom.render-fixture
  "JVM fixture of the v2 DOM render tests (phase-d design §5.3, addendum
   §3.8.12). Each test body runs twice: on an inline world, and on
   `{:inline? false :budget 8}`, both with a manual executor the test
   steps, in verify mode. Reads go through `value-async` while the
   executor is pumped: a blocking read would wait for steps the test must
   take. Exhaustion is an empty executor queue after pumping, which the
   handoff guarantees whenever work is pending."
  (:require [clojure.test :refer [is testing]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.dom.discharge :as disch])
  (:import [java.util.concurrent Executor LinkedBlockingQueue]))

(defn manual-executor
  "[executor queue]: the executor keeps its runnables until the test runs them."
  []
  (let [q (LinkedBlockingQueue.)]
    [(reify Executor (execute [_ r] (.add q r))) q]))

(defn pump!
  "Runs the queued runnables until none is left. Returns how many ran."
  [^LinkedBlockingQueue q]
  (loop [n 0]
    (if-let [r (.poll q)]
      (do (.run ^Runnable r) (recur (inc n)))
      n)))

(def configs
  "The two world configurations every test runs on."
  [{:label "inline" :opts {}}
   {:label "non-inline, budget 8" :opts {:inline? false :budget 8}}])

(defn with-world
  "Calls `(f env)` with a fresh verify-mode world bound, made with `opts`
   and a manual executor. env: :w, :q, :inline?, :settle! (pump to
   exhaustion), and the mock discharge's map under :mock."
  [opts f]
  (let [[ex q] (manual-executor)
        divergences (atom [])
        w (v2/world (merge {:verify? true :hook (verify/checking-hook divergences) :executor ex} opts))
        env {:w w :q q :inline? (not (false? (:inline? opts)))
             :settle! #(pump! q)
             :mock (mock/make-mock)}]
    (disch/collect-violations!)
    (try
      (binding [v2/*world* w] (f env))
      (finally
        (v2/release-world! w)
        (pump! q)
        (is (empty? @divergences) (str "Rule R divergences: " (vec (take 3 @divergences))))))))

(defn each-world
  "Calls `(f env)` once per configuration, each in its own `testing`."
  [f]
  (doseq [{:keys [label opts]} configs]
    (testing label (with-world opts f))))

(defn settle!
  "Pumps `env`'s executor to exhaustion."
  [env]
  ((:settle! env)))

(defn call!
  "Calls `(f)` on another thread while pumping `env`'s executor, and returns
   its value (or throws its throw). For host operations that wait for their
   item, which a non-inline world processes only when the test pumps."
  [env f]
  (let [fut (future (f))]
    (loop []
      (settle! env)
      (if (realized? fut)
        (do (settle! env) @fut)
        (do (Thread/sleep 1) (recur))))))

(defn read!
  "The settled value of `h`, read with value-async while pumping. Throws
   an error result."
  [env h]
  (let [p (promise)]
    (v2/value-async h (fn [v err?] (deliver p [v err?])))
    (loop [i 0]
      (settle! env)
      (if (realized? p)
        (let [[v err?] @p] (if err? (throw v) v))
        (if (< i 5000)
          (do (Thread/sleep 1) (recur (inc i)))
          (throw (ex-info "read! timed out" {})))))))

(defn render!
  "render! of root `h` on `env`'s mock with container :container; settles.
   Returns the control map."
  [env h]
  (let [ctl (render/render! :container h (:discharge (:mock env)))]
    (settle! env)
    ctl))

(defn unmount! [env ctl] (call! env (:unmount! ctl)) (settle! env))
(defn stop! [env ctl] (call! env (:stop! ctl)) (settle! env))

(defn write!
  "Writes `v` to source `h` (a host item; it does not wait) and settles."
  [env h v]
  (v2/write! h v)
  (settle! env))

(defn closed?
  "Whether a torn-down mount left nothing: the mock's registry, the store,
   the ledger, the hooks table and the deferred queue are empty, the
   committed vdom is nil, and the container has no children."
  [env state]
  (let [{:keys [elements discharge]} (:mock env)]
    (and (= :unmounted (render/phase state))
         (empty? @elements)
         (empty? (mock/children discharge :container))
         (render/clean? state))))

(defn violations
  "The integrity violations collected since the last drain."
  []
  (disch/drain-violations!))
