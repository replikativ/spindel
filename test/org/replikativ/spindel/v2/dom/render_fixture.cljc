(ns org.replikativ.spindel.v2.dom.render-fixture
  "Fixture of the v2 DOM render tests (phase-d design §5.3, addendum
   §3.8.12). On the JVM each test body runs twice: on an inline world, and
   on `{:inline? false :budget 8}`, both with a manual executor the test
   steps, in verify mode. Reads go through `value-async` while the
   executor is pumped: a blocking read would wait for steps the test must
   take. Exhaustion is an empty executor queue after pumping, which the
   handoff guarantees whenever work is pending.

   On CLJS a body runs once, on an inline world without a time slice: its
   operations complete before they return (within the budget), so settling
   is a no-op and reads answer synchronously."
  (:require #?(:clj [clojure.test :refer [is testing]]
               :cljs [cljs.test :refer-macros [is testing]])
            [org.replikativ.spindel.v2.core :as v2]
            #?(:clj [org.replikativ.spindel.v2.verify :as verify])
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.dom.discharge :as disch])
  #?(:clj (:import [java.util.concurrent Executor LinkedBlockingQueue])))

#?(:clj
   (defn manual-executor
     "[executor queue]: the executor keeps its runnables until the test runs them."
     []
     (let [q (LinkedBlockingQueue.)]
       [(reify Executor (execute [_ r] (.add q r))) q])))

(def max-steps
  "A deadline on every loop of the fixture: a run that does not settle in
   this many steps fails instead of hanging."
  100000)

(def wait-ms
  "A deadline on every wait of the fixture, in milliseconds."
  10000)

#?(:clj
   (defn pump!
     "Runs the queued runnables until none is left. Returns how many ran.
      Throws after `max-steps` runnables (work that never settles)."
     [^LinkedBlockingQueue q]
     (loop [n 0]
       (if-let [r (.poll q)]
         (if (< n max-steps)
           (do (.run ^Runnable r) (recur (inc n)))
           (throw (ex-info "pump!: the world did not settle" {:steps n})))
         n))))

(def configs
  "The world configurations every test runs on."
  #?(:clj [{:label "inline" :opts {}}
           {:label "non-inline, budget 8" :opts {:inline? false :budget 8}}]
     ;; no time slice: a turn ends only at its budget, so an inline
     ;; operation completes before it returns however slow the host is
     :cljs [{:label "inline" :opts {:slice-ms nil}}]))

(defn with-world
  "Calls `(f env)` with a fresh world bound, made with `opts` (JVM: in
   verify mode, with a manual executor). env: :w, :inline?, :settle!, the
   mock discharge's map under :mock, and on the JVM the executor's queue
   under :q."
  [opts f]
  #?(:clj
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
           (is (empty? @divergences) (str "Rule R divergences: " (vec (take 3 @divergences)))))))
     :cljs
     (let [w (v2/world opts)
           env {:w w :inline? true :settle! (constantly 0) :mock (mock/make-mock)}]
       (disch/collect-violations!)
       (try
         (binding [v2/*world* w] (f env))
         (finally (v2/release-world! w))))))

#?(:cljs
   (defn guard-done
     "`done` of an async test with a deadline: if it is not called within
      `wait-ms`, the test fails and ends instead of hanging. Idempotent."
     [done]
     (let [fin (atom false)
           t (js/setTimeout (fn []
                              (when (compare-and-set! fin false true)
                                (is false (str "the test did not finish within " wait-ms " ms"))
                                (done)))
                            wait-ms)]
       (fn []
         (when (compare-and-set! fin false true)
           (js/clearTimeout t)
           (done))))))

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
  "Calls `(f)` and returns its value. JVM: on another thread while pumping
   `env`'s executor, for host operations that wait for their item, which a
   non-inline world processes only when the test pumps."
  [env f]
  #?(:clj (let [fut (future (f))
                deadline (+ (System/currentTimeMillis) wait-ms)]
            (loop []
              (settle! env)
              (cond (realized? fut) (do (settle! env) @fut)
                    (> (System/currentTimeMillis) deadline)
                    (do (future-cancel fut)
                        (throw (ex-info "call!: no answer before the deadline" {:ms wait-ms})))
                    :else (do (Thread/sleep 1) (recur)))))
     :cljs (f)))

(defn read!
  "The settled value of `h`, read with value-async while pumping. Throws
   an error result."
  [env h]
  #?(:clj (let [p (promise)]
            (v2/value-async h (fn [v err?] (deliver p [v err?])))
            (loop [i 0]
              (settle! env)
              (if (realized? p)
                (let [[v err?] @p] (if err? (throw v) v))
                (if (< i 5000)
                  (do (Thread/sleep 1) (recur (inc i)))
                  (throw (ex-info "read! timed out" {}))))))
     :cljs (let [r (volatile! ::none)]
             (v2/value-async h (fn [v err?] (vreset! r [v err?])))
             (let [[v err? :as x] @r]
               (cond (= ::none x) (throw (ex-info "read!: not settled synchronously" {}))
                     err? (throw v)
                     :else v)))))

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

(defn run-deferred!
  "Runs the mock's deferred work (the deferred-effect flushes) and settles."
  [env]
  (mock/run-deferred! (:discharge (:mock env)))
  (settle! env))

(defn leftovers
  "What a torn-down mount left behind, as a vector of keywords; empty when
   the mock's registry, the store, the ledger, the container and the mock's
   live tree model are empty, the committed vdom is nil and the phase is
   :unmounted."
  [env state]
  (let [{:keys [elements discharge]} (:mock env)]
    (cond-> []
      (not= :unmounted (render/phase state)) (conj [:phase (render/phase state)])
      (seq @elements) (conj :registry)
      (seq (mock/children discharge :container)) (conj :container)
      (some pos? (vals (mock/live-state discharge))) (conj [:mock-live (mock/live-state discharge)])
      (not (render/clean? state)) (conj :mount-state))))

(defn violations
  "The integrity violations collected since the last drain."
  []
  (disch/drain-violations!))
