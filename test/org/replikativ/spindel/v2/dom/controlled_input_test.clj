(ns org.replikativ.spindel.v2.dom.controlled-input-test
  "Controlled-input restore, the synchronous subset (C6 in P4, phase-d
   addendum §3.8.10, tests CB5a-CB5i on the JVM mock). An element is
   controlled when its committed attrs hold :value or :checked. After a
   handler on it returns, the wrapper waits for the root to settle and the
   mount to commit its newest delivery; then the committed attr is the
   world's answer and the DOM property is set to it. A restore happens only
   if it completes before the wrapper returns: otherwise an expiry token
   makes every late path (a queued callback, a pending entry in a later
   flush) do nothing. The jsdom versions are in controlled_input_cljs_test."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(defn- digits? [s] (boolean (re-matches #"\d*" (str s))))

(defn- d [env] (:discharge (:mock env)))

(defn- input-el
  "The mock element of the input, the first child of the root's div."
  [env state]
  (get @(:elements (:mock env)) (:addr (first (:children (render/committed state))))))

(defn- type!
  "The user types: the property changes, then the input event fires."
  [env el text]
  (mock/set-prop! (d env) el :value text)
  ((get (mock/attrs-of (d env) el) :on-input) {:target el}))

(defn- prop-writes [env] (filterv #(= :set-prop (:op %)) @(:log (:mock env))))

(defn- digits-root
  "A div with a controlled text input of `t` (rejecting non-digits) and the
   text of `u`; `extra` runs in the handler after the check."
  [env t u extra]
  (let [h (fn [e]
            (let [s (mock/prop (d env) (:target e) :value)]
              (when (digits? s) (reset! t s))
              (extra)))]
    (spin (let [v (iv/get-new (track t)) x (iv/get-new (track u))]
            (el/div (el/input {:value v :on-input h}) (str x))))))

(defn- mount [env extra]
  (let [t (v2/signal "12")
        u (v2/signal 0)
        {:keys [state] :as ctl} (fx/render! env (digits-root env t u #(extra u)))]
    {:t t :u u :state state :ctl ctl :el (input-el env state)}))

(deftest cb5a-a-rejected-keystroke-is-reverted
  (fx/with-world
    {}
    (fn [env]
      (let [{:keys [el ctl]} (mount env (fn [_]))]
        (type! env el "12a")
        (is (= "12" (mock/prop (d env) el :value)) "before the handler returns")
        (is (= [{:op :set-prop :el el :prop :value :value "12"}] (prop-writes env)))
        (fx/unmount! env ctl)))))

(deftest cb5b-rejected-with-an-unrelated-commit
  (fx/with-world
    {}
    (fn [env]
      (let [{:keys [el state ctl]} (mount env #(swap! % inc))]
        (type! env el "12a")
        (is (= 2 (render/revision state)) "the unrelated commit lands")
        (is (= "12" (mock/prop (d env) el :value)) "and the value is restored")
        (fx/unmount! env ctl)))))

(deftest cb5c-accepted-but-deferred
  (fx/with-world
    {:budget 8}
    (fn [env]
      (let [t (v2/signal "12")
            mids (vec (for [i (range 40)] (spin (count (iv/get-new (track t))))))
            h (fn [e] (let [s (mock/prop (d env) (:target e) :value)] (when (digits? s) (reset! t s))))
            root (spin (let [v (iv/get-new (track t))]
                         (loop [i 0 acc 0]
                           (if (< i (count mids))
                             (recur (inc i) (+ acc (v2/await (nth mids i))))
                             (el/div (el/input {:value v :on-input h}) (str acc))))))
            {:keys [state] :as ctl} (fx/render! env root)
            el (input-el env state)]
        (type! env el "123")
        (is (= 1 (render/revision state)) "the commit has not landed: the check is withdrawn")
        (is (= "123" (mock/prop (d env) el :value)) "the typed value stays")
        (fx/settle! env)
        (is (= 2 (render/revision state)))
        (is (= "123" (mock/prop (d env) el :value)) "the later commit sets the same value")
        (is (empty? (prop-writes env)) "no restore write")
        (fx/unmount! env ctl)))))

(deftest cb5d-a-rejected-checkbox-toggle-is-reverted
  (fx/with-world
    {}
    (fn [env]
      (let [c (v2/signal false)
            h (fn [_] nil)                        ; the toggle is rejected
            root (spin (el/div (el/input {:type "checkbox" :checked (iv/get-new (track c)) :on-change h})))
            {:keys [state] :as ctl} (fx/render! env root)
            el (input-el env state)]
        (mock/set-prop! (d env) el :checked true)
        ((get (mock/attrs-of (d env) el) :on-change) {:target el})
        (is (false? (mock/prop (d env) el :checked)))
        (fx/unmount! env ctl)))))

(deftest cb5e-an-accepted-keystroke-is-not-touched
  (fx/with-world
    {}
    (fn [env]
      (let [{:keys [el state ctl]} (mount env (fn [_]))]
        (type! env el "123")
        (is (= 2 (render/revision state)) "one commit")
        (is (= "123" (mock/prop (d env) el :value)))
        (is (empty? (prop-writes env)) "no restore write")
        (fx/unmount! env ctl)))))

(deftest cb5f-a-non-inline-world-does-not-restore
  (fx/with-world
    {:inline? false :budget 8}
    (fn [env]
      (let [{:keys [el ctl]} (mount env (fn [_]))]
        (type! env el "12a")
        (fx/settle! env)
        (is (= "12a" (mock/prop (d env) el :value)) "the P4 scope: no asynchronous restore")
        (is (empty? (prop-writes env)))
        (fx/unmount! env ctl)))))

(deftest cb5g-a-queued-callback-after-the-withdrawal
  (fx/with-world
    {:budget 2}
    (fn [env]
      (let [{:keys [el ctl]} (mount env (fn [_]))]
        ;; two items ahead of the handler's wait: its callback is queued, not run
        (v2/no-inline (dotimes [_ 2] (v2/host! (:w env) (fn []))))
        (type! env el "12a")
        (is (= "12a" (mock/prop (d env) el :value)) "no restore before the wrapper returned")
        (mock/set-prop! (d env) el :value "999")  ; a later keystroke, not yet processed
        (fx/settle! env)
        (is (= "999" (mock/prop (d env) el :value)) "the late callback writes nothing")
        (is (empty? (prop-writes env)))
        (fx/unmount! env ctl)))))

(deftest cb5h-the-callback-defers-to-a-flush-that-spills
  ;; a write queued before the handler: the wait's callback runs with the
  ;; mount's delivery stored and leaves the restore to the flush; for some
  ;; budget the flush is past it
  (let [hit (atom nil)]
    (doseq [budget (range 3 12) :while (nil? @hit)]
      (fx/with-world
        {:budget budget}
        (fn [env]
          (let [{:keys [el u state ctl]} (mount env (fn [_]))]
            (v2/no-inline (v2/write! u 1))
            (type! env el "12a")
            (when (and (seq (:restore-pending @state)) (:posted? @state))
              (reset! hit budget)
              (is (= "12a" (mock/prop (d env) el :value)) "no restore before the wrapper returned")
              (fx/settle! env)
              (is (= 2 (render/revision state)) "the flush commits")
              (is (= "12a" (mock/prop (d env) el :value)) "but does not restore")
              (is (empty? (prop-writes env))))
            (fx/settle! env)
            (fx/unmount! env ctl)))))
    (is (some? @hit) "a budget at which the callback ran and the flush spilled")))

(deftest cb5i-liveness
  (testing "the handler unmounts the mount"
    (fx/with-world
      {}
      (fn [env]
        (let [ctl (volatile! nil)
              {:keys [el state] :as m} (mount env (fn [_] ((:unmount! @ctl))))]
          (vreset! ctl (:ctl m))
          (type! env el "12a")
          (is (= :unmounted (render/phase state)))
          (is (empty? (prop-writes env)) "no restore, no throw")))))
  (testing "the handler removes the target's element"
    (fx/with-world
      {}
      (fn [env]
        (let [t (v2/signal "12")
              show (v2/signal true)
              h (fn [_] (reset! show false))
              root (spin (let [v (iv/get-new (track t)) sh (iv/get-new (track show))]
                           (el/div (when sh (el/input {:value v :on-input h})))))
              {:keys [state] :as ctl} (fx/render! env root)
              el (input-el env state)]
          (type! env el "12a")
          (is (= [[:div {}]] (mock/dom (d env) :container)))
          (is (empty? (prop-writes env)) "no restore, no throw")
          (fx/unmount! env ctl))))))
