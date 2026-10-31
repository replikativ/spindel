(ns org.replikativ.spindel.engine.public-world-selection-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.lifecycle :as lifecycle]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :as h :refer [async with-ctx run-spin!]]))

(deftest legacy-selected-world-await-restores-its-lexical-and-caller-contexts
  (async done
         (with-redefs [h/create-test-context #(ctx/create-execution-context :engine :simple :executor (ex/synchronous-executor))]
           (with-ctx [a]
             (let [b (ctx/fork-context a)
                   events (atom [])
                   label (fn [] (cond (ec/same-world? ec/*execution-context* a) :a
                                      (ec/same-world? ec/*execution-context* b) :b
                                      :else :unknown))
                   df (sync/create-deferred b)
                   target (binding [ec/*execution-context* b]
                            (spin (swap! events conj [:body (label)])
                                  (let [value (await df)]
                                    (swap! events conj [:body-resumed (label) value])
                                    value)))
                   actor (spin (swap! events conj [:actor-start (label)])
                               (let [value (binding [ec/*execution-context* b]
                                             (let [value (await target)]
                                               (swap! events conj [:inside-binding (label) value])
                                               value))]
                                 (swap! events conj [:after-binding (label) value])
                                 value))]
               (run-spin! actor
                          (fn [value]
                            (swap! events conj [:callback (label) value])
                            (is (= 42 value))
                            (is (= [[:actor-start :a] [:body :b] [:body-resumed :b 42]
                                    [:inside-binding :b 42] [:after-binding :a 42] [:callback :a 42]]
                                   @events))
                            (done))
                          (fn [error]
                            (is false (str error))
                            (done)))
          ;; Synchronous dispatch has returned from the real unassigned wait.
          ;; Delivery below must resume it, rather than taking an inline cache.
               (is (= [[:actor-start :a] [:body :b]] @events))
               (is (false? (:assigned? (rtp/read-public-deferred b df))))
               (binding [ec/*execution-context* b] (sync/deliver! df 42)))))))

(defn- finish-native! [runtime]
  (let [joined (atom []) errors (atom [])]
    (lifecycle/observe! (rtp/request-world-release! runtime :context-test-finished)
                        #(swap! joined conj %) #(swap! errors conj %))
    (is (= [nil] @joined))
    (is (empty? @errors))
    (verify-boundaries! runtime)))

(defn- native-child [runtime id]
  (:context (rtp/fork-owned-world! runtime {:world-id id :owner (lifetime/root-scope runtime)})))

(deftest ordinary-context-capture-keeps-the-raw-bindings-api
  (let [bindings (with-meta {:address :lexical} {:scope :metadata})
        current {:bindings bindings :other :preserved}
        captured (ec/capture-context-scope current)]
    (is (identical? bindings captured))
    (is (= {:scope :metadata} (meta captured)))
    (is (identical? current (ec/restore-context-scope captured current)))
    (is (nil? (ec/capture-context-scope nil)))
    (is (nil? (ec/restore-context-scope captured nil)))
    (is (= {:bindings nil :other :preserved}
           (ec/restore-context-scope nil {:other :preserved})))))

(deftest explicit-native-selection-survives-a-real-park
  (let [a (c/runtime {:audit? true :cps-exit? true}) b (native-child a [:w 1])
        gate (c/ticket :selection) events (atom []) errors (atom []) values (atom [])
        task (c/cspin a :selection
                      (binding [ec/*execution-context* b]
                        (swap! events conj [:before (boolean (ec/same-world? ec/*execution-context* b))])
                        (c/park gate)
                        (swap! events conj [:inside (boolean (ec/same-world? ec/*execution-context* b))
                                            (boolean (ec/same-world? (rtp/context-scope-runner b) a))]))
                      (swap! events conj [:after (boolean (ec/same-world? ec/*execution-context* a))])
                      :done)]
    (try
      (c/observe! a task #(swap! values conj %) #(swap! errors conj %))
      (is (= [[:before true]] @events))
      (is (= :parked (get-in (c/snapshot a) [:runs [:selection 1] :status])))
      (c/resume-ticket! a (c/pending-ticket a gate) :resume)
      (is (= [[:before true] [:inside true true] [:after true]] @events))
      (is (= [:done] @values))
      (is (empty? @errors))
      (verify-boundaries! a)
      (finally (finish-native! a)))))

(deftest copied-native-run-keeps-literals-and-rebases-both-binding-exits
  (let [a (c/runtime {:audit? true :cps-exit? true}) b (native-child a [:w 1])
        d (native-child a [:w 2]) gate (c/ticket :nested-selection)
        events (atom []) errors (atom []) child (atom nil)
        label (fn [context]
                (cond (ec/same-world? context a) :a
                      (ec/same-world? context b) :b
                      (ec/same-world? context d) :d
                      (and @child (ec/same-world? context @child)) :c
                      :else :unknown))
        task (c/cspin a :nested-selection
                      (binding [ec/*execution-context* b]
                        (binding [ec/*execution-context* d]
                          (swap! events conj [:before (label ec/*execution-context*)])
                          (c/park gate)
                          (swap! events conj [:inner (label ec/*execution-context*)
                                              (label (rtp/context-scope-runner ec/*execution-context*))]))
                        (swap! events conj [:outer (label ec/*execution-context*)]))
                      (swap! events conj [:after (label ec/*execution-context*)])
                      :done)]
    (try
      (c/observe! a task (fn [_]) #(swap! errors conj %))
      (reset! child (native-child a [:w 3]))
      (is (= :inherited (get-in (c/snapshot @child) [:runs [:nested-selection 1] :status])))
      (c/resume-ticket! @child (c/pending-ticket @child gate) :copy)
      (is (= [[:before :d] [:inner :d :c] [:outer :b] [:after :c]] @events))
      (is (= :parked (get-in (c/snapshot a) [:runs [:nested-selection 1] :status])))
      (c/resume-ticket! a (c/pending-ticket a gate) :source)
      (is (= [[:before :d] [:inner :d :c] [:outer :b] [:after :c]
              [:inner :d :a] [:outer :b] [:after :a]] @events))
      (is (empty? @errors))
      (verify-boundaries! a)
      (finally (finish-native! a)))))

(deftest literal-selection-exits-through-error-and-finally
  (let [a (c/runtime {:audit? true :cps-exit? true}) b (native-child a [:w 1])
        gate (c/ticket :error-selection) events (atom []) errors (atom []) values (atom [])
        task (c/cspin a :error-selection
                      (try
                        (binding [ec/*execution-context* b]
                          (try
                            (c/park gate)
                            (throw (ex-info "selection-error" {}))
                            (finally
                              (swap! events conj [:finally (boolean (ec/same-world? ec/*execution-context* b))]))))
                        (catch #?(:clj Exception :cljs :default) error
                          (swap! events conj [:caught (ex-message error)
                                              (boolean (ec/same-world? ec/*execution-context* a))])))
                      :done)]
    (try
      (c/observe! a task #(swap! values conj %) #(swap! errors conj %))
      (c/resume-ticket! a (c/pending-ticket a gate) :resume)
      (is (= [[:finally true] [:caught "selection-error" true]] @events))
      (is (= [:done] @values))
      (is (empty? @errors))
      (verify-boundaries! a)
      (finally (finish-native! a)))))

(deftest a-released-literal-remains-identifiable-without-effect-admission
  (let [a (c/runtime {:audit? true :cps-exit? true})
        publication (rtp/fork-owned-world! a {:world-id [:w 1] :owner (lifetime/root-scope a)})
        b (:context publication) gate (c/ticket :released-selection)
        events (atom []) errors (atom []) values (atom []) saved (atom nil)
        task (c/cspin a :released-selection
                      (binding [ec/*execution-context* b]
                        (reset! saved (ec/capture-context-scope b))
                        (c/park gate)
                        (let [before (c/snapshot-family a)
                              error (try (rtp/register-computation! b nil :never-entered (fn [_ _])) nil
                                         (catch #?(:clj Exception :cljs :default) error error))]
                          (swap! events conj [:literal (boolean (ec/same-world? ec/*execution-context* b))
                                              (boolean error)])
                          (is (= before (c/snapshot-family a)))))
                      (swap! events conj [:after (boolean (ec/same-world? ec/*execution-context* a))])
                      :done)]
    (try
      (c/observe! a task #(swap! values conj %) #(swap! errors conj %))
      (let [discarded (atom [])]
        (lifecycle/observe! (rtp/discard-owned-world! a (:capability publication) (lifetime/root-scope a) {})
                            #(swap! discarded conj %) #(swap! errors conj %))
        (is (= [nil] @discarded)))
      (is (= :released (:status (c/snapshot b))))
      (is (ec/same-world? b (ec/restore-context-scope @saved a)))
      (c/resume-ticket! a (c/pending-ticket a gate) :resume)
      (is (= [[:literal true true] [:after true]] @events))
      (is (= [:done] @values))
      (is (empty? @errors))
      (is (nil? (get-in (c/snapshot a) [:entities :never-entered])))
      (verify-boundaries! a)
      (finally (finish-native! a)))))

(deftest tagged-runner-exit-cannot-invent-a-missing-activation
  (let [a (c/runtime {:audit? true :cps-exit? true}) b (native-child a [:w 1])
        gate (c/ticket :runner-exit) saved (atom nil) errors (atom [])
        task (c/cspin a :runner-exit
                      (reset! saved (ec/capture-context-binding a))
                      (c/park gate)
                      :done)]
    (try
      (c/observe! a task (fn [_]) #(swap! errors conj %))
      (let [before (c/snapshot-family a)
            error (try (ec/restore-context-binding @saved b b) nil
                       (catch #?(:clj Exception :cljs :default) error error))]
        (is (= ::ec/missing-context-runner (:error (ex-data error))))
        (is (= before (c/snapshot-family a))))
      (c/resume-ticket! a (c/pending-ticket a gate) :resume)
      (is (empty? @errors))
      (finally (finish-native! a)))))

(deftest literal-legacy-data-context-keeps-native-owner-transport-on-fork
  (let [a (c/runtime {:audit? true :cps-exit? true})
        b (ctx/create-execution-context :engine :simple :executor (ex/synchronous-executor))
        gate (c/ticket :legacy-selection) child (atom nil)
        events (atom []) errors (atom []) values (atom []) cells (atom [])
        label (fn [context]
                (cond (ec/same-world? context a) :a
                      (and @child (ec/same-world? context @child)) :c
                      :else :unknown))
        task (c/cspin a :legacy-selection
                      (let [owner (lifetime/current-scope a)]
                        (lifetime/with-owner owner
                          (binding [ec/*execution-context* b]
                            (c/park gate)
                            (let [runner (rtp/context-scope-runner b)
                                  current (lifetime/current-scope runner)
                                  cell (rtp/allocate-runtime-cell! b :application-data {})]
                              (swap! cells conj cell)
                              (swap! events conj [:inside (boolean (ec/same-world? ec/*execution-context* b))
                                                  (label runner)
                                                  (identical? current (rtp/bindable-execution-owner runner current))])
                              (is (= (lifetime/root-scope b)
                                     (rtp/get-state b [:atoms (:id cell) :lifetime/owner])))))))
                      (swap! events conj [:after (label ec/*execution-context*)])
                      :done)]
    (try
      (c/observe! a task #(swap! values conj %) #(swap! errors conj %))
      (reset! child (native-child a [:w 1]))
      (c/resume-ticket! @child (c/pending-ticket @child gate) :copy)
      (is (= [[:inside true :c true] [:after :c]] @events))
      (c/resume-ticket! a (c/pending-ticket a gate) :source)
      (is (= [[:inside true :c true] [:after :c] [:inside true :a true] [:after :a]] @events))
      (is (= [:done] @values))
      (is (empty? @errors))
      (doseq [cell @cells] (is (= :application-data (rtp/runtime-cell-value b (:id cell)))))
      (verify-boundaries! a)
      (finally
        (finish-native! a)
        (ctx/stop-context! b)))))
