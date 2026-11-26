(ns org.replikativ.spindel.v2.scheduler-cljc-test
  "The handoff primitive and the turn's time slice (H2). A drain that needs
   many chained turns hands off without the zero-delay timer's clamp
   (CLJS: setImmediate, else one MessageChannel, else setTimeout; never a
   microtask), each handed-off thunk isolated. A turn also ends after its
   time slice, between units, and hands off; the work completes in order."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is async]])
            [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.host :as hs])
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.core :refer [task]])))

(defn- now-ms []
  #?(:clj (/ (System/nanoTime) 1e6)
     :cljs (if (exists? js/performance) (.now js/performance) (js/Date.now))))

(defn- busy! [ms]
  (let [t0 (now-ms)]
    (loop [] (when (< (- (now-ms) t0) ms) (recur)))))

;; ---------------------------------------------------------------------------
;; Handoff latency: a budget of one unit makes every host item its own turn

(def ^:private n-turns 400)
;; Far below the 4 ms clamp of nested zero-delay timers in browsers, and
;; below node's 1 ms minimum timer delay too.
(def ^:private bound-ms (* n-turns 0.25))

(defn- drain-chain!
  "In a fresh non-inline world with a budget of one unit, `n-turns` host
   writes followed by a read: `n-turns` chained turns. Calls `(cb ms v)`
   with the elapsed time and the read value."
  [cb]
  (let [w (v2/world {:inline? false :budget 1})
        s (binding [v2/*world* w] (v2/signal 0))
        t0 (now-ms)]
    (dotimes [i n-turns] (v2/write! s (inc i)))
    #?(:clj (let [v (v2/value s 10000 ::timeout)]
              (v2/release-world! w)
              (cb (- (now-ms) t0) v))
       :cljs (v2/value-async s (fn [v _err?]
                                 (let [ms (- (now-ms) t0)]
                                   (v2/release-world! w)
                                   ;; outside the callback's gate
                                   (js/setTimeout #(cb ms v) 0)))))))

(defn- check-chain [ms v]
  (is (= n-turns v))
  (is (< ms bound-ms) (str n-turns " chained turns took " ms " ms (bound " bound-ms " ms)")))

(deftest chained-turns-hand-off-without-a-clamp
  ;; the first round warms up the code paths; the second one is measured
  #?(:clj (drain-chain! (fn [_ _] (drain-chain! check-chain)))
     :cljs (async done (drain-chain! (fn [_ _] (drain-chain! (fn [ms v] (check-chain ms v) (done))))))))

;; ---------------------------------------------------------------------------
;; The handoff primitive (CLJS): selection order, FIFO and isolation

#?(:cljs
   (defn- env
     "A host environment with spies on the scheduling functions named by
      `ks` (:setImmediate :MessageChannel :setTimeout); each records its use
      in `calls`, then delegates to a real macrotask."
     [calls ks]
     (let [o #js {}]
       (doseq [k ks]
         (case k
           :setImmediate (set! (.-setImmediate o) (fn [f] (swap! calls conj :setImmediate) (js/setTimeout f 0)))
           :MessageChannel (set! (.-MessageChannel o) (fn [] (swap! calls conj :MessageChannel) (js/MessageChannel.)))
           :setTimeout (set! (.-setTimeout o) (fn [f ms] (swap! calls conj :setTimeout) (js/setTimeout f ms)))))
       o)))

#?(:cljs
   (defn- catching-uncaught!
     "Counts uncaught errors carrying `::boom` instead of letting them reach
      the host (node: process exit). Returns a fn that uninstalls it."
     [caught]
     (let [boom? #(::boom (ex-data %))]
       (if (and (exists? js/process) (fn? (.-on js/process)))
         (let [h (fn [e] (if (boom? e) (swap! caught inc) (throw e)))]
           (.on js/process "uncaughtException" h)
           #(.removeListener js/process "uncaughtException" h))
         (let [h (fn [ev] (when (boom? (.-error ev)) (.preventDefault ev) (swap! caught inc)))]
           (.addEventListener js/window "error" h)
           #(.removeEventListener js/window "error" h))))))

#?(:cljs
   (defn- run-thunks!
     "Schedules thunks :a, a throwing one, :c and :d through the primitive
      `hs/macrotask` selects from `env`, then calls `(cb log caught)`."
     [env cb]
     (let [later! (hs/macrotask env)
           log (atom [])
           caught (atom 0)
           uninstall (catching-uncaught! caught)
           t0 (now-ms)]
       (later! #(swap! log conj :a))
       (later! #(throw (ex-info "boom" {::boom true})))
       (later! #(swap! log conj :c))
       (later! #(swap! log conj :d))
       ((fn poll []
          (if (or (= 3 (count @log)) (> (- (now-ms) t0) 2000))
            ;; one more macrotask: the uncaught error is reported by then
            (js/setTimeout #(do (uninstall) (cb @log @caught)) 5)
            (js/setTimeout poll 1)))))))

#?(:cljs
   (deftest the-primitive-prefers-setImmediate
     (async done
            (let [calls (atom [])]
              (run-thunks! (env calls [:setImmediate :MessageChannel :setTimeout])
                           (fn [log caught]
                             (is (= [:a :c :d] log) "FIFO; a throwing thunk drops none of the others")
                             (is (= 1 caught))
                             (is (= [:setImmediate :setImmediate :setImmediate :setImmediate] @calls))
                             (done)))))))

#?(:cljs
   (deftest without-setImmediate-one-MessageChannel-carries-the-thunks
     (async done
            (let [calls (atom [])]
              (run-thunks! (env calls [:MessageChannel :setTimeout])
                           (fn [log caught]
                             (is (= [:a :c :d] log) "FIFO; a throwing thunk drops none of the others")
                             (is (= 1 caught))
                             (is (= [:MessageChannel] @calls) "one channel, no timer")
                             (done)))))))

#?(:cljs
   (deftest without-both-setTimeout-is-the-fallback
     (async done
            (let [calls (atom [])]
              (run-thunks! (env calls [:setTimeout])
                           (fn [log caught]
                             (is (= [:a :c :d] log) "FIFO; a throwing thunk drops none of the others")
                             (is (= 1 caught))
                             (is (= [:setTimeout :setTimeout :setTimeout :setTimeout] @calls))
                             (done)))))))

;; ---------------------------------------------------------------------------
;; The time slice: cheap budget units, expensive slices

(def ^:private k-tasks 8)
(def ^:private slice-cost-ms 2)

(defn- expensive-slices!
  "One host item of a non-inline world (time slice `slice-ms`, opts merged)
   creates `k-tasks` tasks whose single slices each take `slice-cost-ms` and
   log their index. Calls `(cb log)` once every slice ran (JVM: the last
   entry carries the drainer submissions `subs` counted by then; CLJS: the
   first slice sets a zero-delay timer that logs :probe)."
  [opts subs cb]
  (let [w (v2/world (merge {:inline? false} opts))
        log (atom [])
        handles (atom [])]
    (v2/host! w (fn []
                  (binding [v2/*world* w]
                    (dotimes [i k-tasks]
                      (swap! handles conj
                             (task #?(:cljs (when (zero? i) (js/setTimeout #(swap! log conj :probe) 0)))
                                   (busy! slice-cost-ms)
                                   (swap! log conj (if (and subs (= i (dec k-tasks))) [i @subs] i))
                                   i))))))
    (let [t0 (now-ms)
          done? #(= k-tasks (count (remove #{:probe} @log)))
          finish #(do (v2/release-world! w) (cb @log))]
      #?(:clj (do (loop [] (when (and (not (done?)) (< (- (now-ms) t0) 5000)) (Thread/sleep 1) (recur)))
                  (finish))
         :cljs ((fn poll []
                  (if (or (and (done?) (some #{:probe} @log)) (> (- (now-ms) t0) 5000))
                    (finish)
                    (js/setTimeout poll 1))))))))

#?(:clj
   (defn- counting-executor [subs]
     (reify java.util.concurrent.Executor
       (execute [_ r]
         (swap! subs inc)
         (.execute ^java.util.concurrent.Executor @hs/default-executor r)))))

#?(:clj
   (defn- in-order-with-turns
     "The logged indices and the drainer submissions seen by the last slice."
     [log]
     [(mapv #(if (vector? %) (first %) %) log) (second (peek log))]))

#?(:clj
   (deftest a-turn-ends-after-its-time-slice
     (let [subs (atom 0)]
       (expensive-slices!
        {:slice-ms 5 :executor (counting-executor subs)} subs
        (fn [log]
          (let [[order turns] (in-order-with-turns log)]
            (is (= (vec (range k-tasks)) order) "the order of the slices is unchanged")
            (is (<= 3 turns) (str "the turn ended at the slice and handed off (" turns " turns)"))))))
     (let [subs (atom 0)]
       (expensive-slices!
        {:slice-ms nil :executor (counting-executor subs)} subs
        (fn [log]
          (let [[order turns] (in-order-with-turns log)]
            (is (= (vec (range k-tasks)) order))
            (is (= 1 turns) "without a slice, one turn runs everything")))))))

#?(:cljs
   (deftest a-turn-ends-after-its-time-slice
     ;; a zero-delay timer set by the first slice fires between two turns
     (async done
            (expensive-slices!
             {:slice-ms 5} nil
             (fn [log]
               (is (= (vec (range k-tasks)) (vec (remove #{:probe} log))) "the order of the slices is unchanged")
               (is (not= :probe (peek log)) (str "the turn ended at the slice and handed off: " log))
               (expensive-slices!
                {:slice-ms nil} nil
                (fn [log]
                  (is (= (conj (vec (range k-tasks)) :probe) log) "without a slice, one turn runs everything")
                  (done))))))))
