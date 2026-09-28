(ns org.replikativ.spindel.trace-reuse-test
  "A replay re-runs what its change reaches and adopts the rest: spins
  downstream of the replayed site that the old run computed, and whose
  captures, tracked signals and awaited spins are unchanged, are not
  executed again. Execution counters pin it."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.savepoint :as sp :refer [savepoint]]
            [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.signal :refer [signal]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [outcome (deref result 5000 ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok (first outcome)) (second outcome) (throw (second outcome))))))

(def ^:private runs (atom {}))
(defn- tick! [k] (swap! runs update k (fnil inc 0)))

(defn- replays
  "Run `(make-program root)` once under the payload policy, then replay it
  from its first site once per value of `values` (nil: keep the old value).
  Returns [{:result :runs :trace} ...] for the run and each replay, `:runs`
  counting executions since the run began."
  [make-program values]
  (reset! runs {})
  (let [root (context/create-execution-context)
        session (sp/open! root {:seed 7 :fork-opts {:systems :none}})]
    (try
      (let [t (await-cps (trace/run session (binding [ec/*execution-context* root]
                                              (make-program root))
                                    trace/payload-policy))
            first-site (first (:trace/order t))
            policy (fn [v] (cond->> (trace/keep-policy trace/payload-policy)
                             (some? v) (trace/constrained-policy {first-site v})))]
        (into [{:result (:trace/result t) :runs @runs :trace t}]
              (for [v values
                    :let [t' (await-cps (trace/replay t first-site (policy v)))]]
                {:result (:trace/result t') :runs @runs :trace t'})))
      (finally
        (await-cps (sp/close! session))
        (context/stop-context! root)))))

(defn- sites [trace]
  (mapv #(get-in trace [:trace/entries % :site]) (:trace/order trace)))

(deftest unchanged-downstream-spins-are-adopted
  (let [[run kept changed]
        (replays (fn [_]
                   (spin
                    (let [u (await (spin (tick! :upstream) 10))
                          a (savepoint :a 1)
                          b (savepoint :b 2)
                          on-b (await (spin (tick! :on-b) (* 2 b)))
                          on-a (await (spin (tick! :on-a) (* 3 a)))]
                      [u a b on-b on-a])))
                 [nil 5])]
    (is (= [10 1 2 4 3] (:result run)))
    (testing "a replay that changes nothing executes nothing again"
      (is (= [10 1 2 4 3] (:result kept)))
      (is (= {:upstream 1 :on-b 1 :on-a 1} (:runs kept))))
    (testing "a change re-runs exactly the spins that see it"
      (is (= [10 5 2 4 15] (:result changed)))
      (is (= {:upstream 1 :on-b 1 :on-a 2} (:runs changed))))))

(deftest a-spin-holding-a-site-is-run-again
  (let [[run kept]
        (replays (fn [_]
                   (spin
                    (let [a (savepoint :a 1)
                          inner (await (spin (tick! :inner) (savepoint :inner 7)))]
                      [a inner])))
                 [nil])]
    (is (= [1 7] (:result run)))
    (is (= [1 7] (:result kept)))
    (is (= 2 (:inner (:runs kept))) "its site has to be decided again")
    (is (= [:a :inner] (sites (:trace kept))) "and recorded in the new trace")))

(deftest a-changed-parent-re-runs-and-keeps-its-unchanged-child
  (let [[_ changed]
        (replays (fn [_]
                   (spin
                    (let [a (savepoint :a 1)
                          b (savepoint :b 2)]
                      (await (spin (tick! :outer)
                                   (+ a (await (spin (tick! :leaf) (* 2 b)))))))))
                 [5])]
    (is (= 9 (:result changed)))
    (is (= {:outer 2 :leaf 1} (:runs changed)))))

(deftest a-spin-tracking-a-changed-signal-is-run-again
  (let [[run kept changed]
        (replays (fn [root]
                   (let [s (binding [ec/*execution-context* root] (signal 0))]
                     (spin
                      (let [a (savepoint :a 1)]
                        (reset! s a)
                        (await (spin (tick! :tracker) (* 10 (:new (track s)))))))))
                 [nil 5])]
    (is (= 10 (:result run)))
    (is (= 10 (:result kept)))
    (is (= 1 (:tracker (:runs kept))) "the signal holds the same value")
    (is (= 50 (:result changed)))
    (is (= 2 (:tracker (:runs changed))) "the signal changed")))
