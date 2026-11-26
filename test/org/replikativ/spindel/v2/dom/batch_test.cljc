(ns org.replikativ.spindel.v2.dom.batch-test
  "Write batches for event handlers (C2, phase-d addendum §3.8.9, tests
   CB1, CB3a, CB7-CB10). `batch` runs its body as one host item of the
   world current at the call, with that world bound inside: its writes nest,
   so nothing propagates between them. It does not promise one turn or one
   commit; on an inline world within the budget it gives one commit before
   it returns. The mount wraps every :on-* handler so that it runs with the
   mount's world bound."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render :refer [batch]]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(defn- d [env] (:discharge (:mock env)))

(defn- handler
  "The handler the mount registered for `k` on the element at `addr`: the
   wrapper, as the browser gets it."
  [env addr k]
  (let [el (get @(:elements (:mock env)) addr)]
    (get (mock/attrs-of (d env) el) k)))

(defn- root-of
  "A root over signals a and b that counts its runs, with a button whose
   :on-click calls `on-click`."
  [a b runs on-click]
  (spin (let [x (iv/get-new (track a))
              y (iv/get-new (track b))]
          (swap! runs inc)
          (el/div (el/button {:on-click on-click} "go") (str x "," y)))))

(defn- button-addr [state] (:addr (first (:children (render/committed state)))))

;; ---------------------------------------------------------------------------
;; CB1: two writes in one batch, one commit

(deftest cb1-two-writes-in-a-batch-give-one-commit
  (fx/each-world
   (fn [env]
     (let [a (v2/signal 0)
           b (v2/signal 0)
           runs (atom 0)
           returned (atom nil)
           root (root-of a b runs (fn [_] (batch (reset! a 1) (reset! b 2))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (reset! runs 0)
       ((handler env (button-addr state) :on-click) {})
       (reset! returned [@runs (render/revision state)])
       (fx/settle! env)
       (is (= 1 @runs) "one root run")
       (is (= 2 (render/revision state)) "one commit")
       (when (:inline? env)
         (is (= [1 2] @returned) "before the handler returns (inline, within the budget)"))
       (is (= [[:div {} [:button {} "go"] "1,2"]] (mock/dom (d env) :container)))
       (fx/unmount! env ctl)))))

(deftest cb1-control-without-batch
  (fx/with-world
    {}
    (fn [env]
      (let [a (v2/signal 0)
            b (v2/signal 0)
            runs (atom 0)
            root (root-of a b runs (fn [_] (reset! a 1) (reset! b 2)))
            {:keys [state] :as ctl} (fx/render! env root)]
        (reset! runs 0)
        ((handler env (button-addr state) :on-click) {})
        (fx/settle! env)
        (is (= 2 @runs))
        (is (= 3 (render/revision state)) "two commits")
        (fx/unmount! env ctl)))))

;; ---------------------------------------------------------------------------
;; CB3a: a source root, two writes in a batch

(defn- vnode [i] (el/div {:id (str "v" i)} (str i)))

(deftest cb3a-a-source-root-coalesces-a-batch
  (fx/each-world
   (fn [env]
     (let [v (v2/signal (vnode 0))
           seen (atom [])
           {:keys [state] :as ctl} (fx/render! env v)]
       (v2/observe! v (fn [x _] (swap! seen conj (:attrs x))))
       (fx/settle! env)
       (batch (reset! v (vnode 1)) (reset! v (vnode 2)))
       (fx/settle! env)
       (is (= [{:id "v0"} {:id "v1"} {:id "v2"}] @seen) "a plain observer sees both callbacks")
       (is (= 2 (render/revision state)) "the mount commits once")
       (is (= [[:div {:id "v2"} "2"]] (mock/dom (d env) :container)) "the newest")
       (fx/unmount! env ctl)))))

;; ---------------------------------------------------------------------------
;; CB7: nested batches run at once

(deftest cb7-nested-batches-run-at-once
  (fx/each-world
   (fn [env]
     (let [log (atom [])
           s (v2/signal 0)
           root (spin (let [x (iv/get-new (track s))]
                        (el/div {:on-commit (fn [_]
                                              (when (zero? x)
                                                (batch (swap! log conj [:effect-batch]))
                                                (swap! log conj [:after-effect-batch])))}
                                (str x))))
           ctl (fx/render! env root)]
       (is (= [[:effect-batch] [:after-effect-batch]] @log) "a batch inside an effect runs at once")
       (reset! log [])
       (batch (batch (swap! log conj :inner)) (swap! log conj :outer))
       (fx/settle! env)
       (is (= [:inner :outer] @log) "a batch inside a batch runs at once")
       (fx/unmount! env ctl)))))

;; ---------------------------------------------------------------------------
;; CB10: a write, then a throw

(deftest cb10-a-write-then-a-throw
  (fx/each-world
   (fn [env]
     (let [a (v2/signal 0)
           root (spin (el/div (str (iv/get-new (track a)))))
           {:keys [state] :as ctl} (fx/render! env root)
           thrown (try (batch (reset! a 1) (throw (ex-info "after the write" {}))) nil
                       (catch #?(:clj Exception :cljs :default) e (ex-message e)))]
       (fx/settle! env)
       (if (:inline? env)
         (is (= "after the write" thrown) "inline, the throw reaches the caller")
         (is (nil? thrown) "queued, it is reported by the processing thread"))
       (is (= [[:div {} "1"]] (mock/dom (d env) :container)) "the first write stays and propagates")
       (is (= 2 (render/revision state)))
       (fx/unmount! env ctl)))))

;; ---------------------------------------------------------------------------
;; CB8, CB9 (JVM)

#?(:clj
   (deftest cb8-a-queued-batch-creates-in-the-callers-world
     (fx/with-world
       {:inline? false :budget 8}
       (fn [env]
         (let [other (v2/world {})
               made (atom nil)]
           (batch (reset! made (v2/signal 0)))
           ;; the drainer runs the item with another world bound
           (binding [v2/*world* other] (fx/settle! env))
           (is (identical? (:w env) (.-w ^org.replikativ.spindel.v2.core.Handle @made))
               "the signal is in the batch's world")
           (v2/release-world! other))))))

#?(:clj
   (deftest cb9-a-batch-whose-drain-spills
     (fx/with-world
       {:budget 8}
       (fn [env]
         (let [a (v2/signal 0)
               b (v2/signal 0)
               seen (atom [])
               ;; enough computations between the sources and the root that
               ;; the drain takes more than one budget
               mids (vec (for [i (range 12)]
                           (spin (let [x (iv/get-new (track a)) y (iv/get-new (track b))]
                                   (swap! seen conj [x y])
                                   (+ i x y)))))
               root (spin (loop [i 0 acc 0]
                            (if (< i (count mids))
                              (recur (inc i) (+ acc (v2/await (nth mids i))))
                              (el/div (str acc)))))
               {:keys [state] :as ctl} (fx/render! env root)]
           (reset! seen [])
           (batch (reset! a 1) (reset! b 2))
           (is (= 1 (render/revision state)) "the commit has not landed when the batch returns")
           (fx/settle! env)
           (is (= 2 (render/revision state)) "it comes in a later turn")
           (is (every? #{[1 2]} @seen) "no computation saw one write without the other")
           (is (= [[:div {} (str (+ 66 36))]] (mock/dom (d env) :container)))
           (fx/unmount! env ctl))))))
