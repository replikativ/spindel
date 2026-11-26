(ns org.replikativ.spindel.v2.dom.browser-cljs-test
  "The v2 DOM on a real DOM (jsdom): the browser discharge, refs on attached
   elements, the deferred hook after a macrotask, two writes in one batched
   handler (CB1), and controlled-input restore, CB5a-CB5i of phase-d
   addendum §3.8.12. Events are dispatched synchronously, as a browser
   does, so \"before the handler returns\" means before dispatchEvent
   returns."
  (:require [cljs.test :refer-macros [deftest is testing async]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render :refer [batch]]
            [org.replikativ.spindel.v2.dom.browser :as browser]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]
            ["jsdom" :refer [JSDOM]]))

(defn- page []
  (let [dom (JSDOM. "<!DOCTYPE html><html><body><div id=\"app\"></div></body></html>")
        doc (.-document (.-window dom))]
    {:win (.-window dom) :doc doc :container (.getElementById doc "app")
     :d (browser/make-dom-discharge doc)}))

(defn- fire! [{:keys [win]} el type]
  (let [E (.-Event win)]
    (.dispatchEvent el (E. type #js {:bubbles true}))))

(defn- type! [p el text]
  (set! (.-value el) text)
  (fire! p el "input"))

(defn- html [p] (.-innerHTML (:container p)))

(defn- with-world
  "Calls `(f w p done)` with a fresh world made with `opts` bound (no time
   slice unless given: a turn ends only at its budget) and a fresh page; the
   test ends at `(done)`."
  [opts f]
  (async done*
         (let [done (fx/guard-done done*)
               w (v2/world (merge {:slice-ms nil} opts))
               p (page)]
           (binding [v2/*world* w]
             (f w p (fn [] (v2/release-world! w) (js/setTimeout done 0)))))))

(defn- later [ms f] (js/setTimeout f ms))

(defn- digits? [s] (boolean (re-matches #"\d*" (str s))))

(defn- mount-input
  "A controlled text input of `t` that rejects non-digits; `extra` runs in
   the handler. Returns {:state :ctl :input :t :u}."
  [p extra]
  (let [t (v2/signal "12")
        u (v2/signal 0)
        h (fn [e]
            (let [s (.. e -target -value)]
              (when (digits? s) (reset! t s))
              (extra u)))
        root (spin (let [v (iv/get-new (track t)) x (iv/get-new (track u))]
                     (el/div (el/input {:value v :on-input h}) (el/span (str x)))))
        {:keys [state] :as ctl} (render/render! (:container p) root (:d p))]
    {:state state :ctl ctl :t t :u u :input (.querySelector (:container p) "input")}))

;; ---------------------------------------------------------------------------
;; The browser discharge

(deftest static-root-render-and-unmount
  (with-world {}
    (fn [_ p done]
      (let [{:keys [state] :as ctl} (render/render! (:container p) (spin (el/div {:id "r"} (el/p "hello"))) (:d p))]
        (is (= "<div id=\"r\"><p>hello</p></div>" (html p)))
        ((:unmount! ctl))
        (is (= "" (html p)))
        (is (render/clean? state))
        (done)))))

(deftest refs-see-attached-elements-and-the-deferred-hook-runs-later
  (with-world {}
    (fn [_ p done]
      (let [log (atom [])
            show (v2/signal true)
            root (spin (el/div (when (iv/get-new (track show))
                                 (el/span {:ref (fn [el] (swap! log conj [:ref (.-isConnected el)])
                                                  #(swap! log conj [:ref-cleanup (.-isConnected el)]))
                                           :on-commit-deferred (fn [el] (swap! log conj [:deferred (.-isConnected el)]))}
                                          "s"))))
            {:keys [state] :as ctl} (render/render! (:container p) root (:d p))]
        (is (= [[:ref true]] @log) "the ref sees a connected element")
        (render/on-deferred state 1
                            (fn [_]
                              (is (= [[:ref true] [:deferred true]] @log) "the deferred hook ran in a later macrotask")
                              ;; the waiter runs under the gate: act from a macrotask of its own
                              (later 0 (fn []
                                         (reset! show false)
                                         (is (= [[:ref true] [:deferred true] [:ref-cleanup true]] @log)
                                             "the cleanup runs while the element is attached")
                                         ((:unmount! ctl))
                                         (done)))))))))

(deftest cb1-two-writes-in-a-batched-handler
  (with-world {}
    (fn [_ p done]
      (let [a (v2/signal 0)
            b (v2/signal 0)
            runs (atom 0)
            root (spin (let [x (iv/get-new (track a)) y (iv/get-new (track b))]
                         (swap! runs inc)
                         (el/div (el/button {:on-click (fn [_] (batch (reset! a 1) (reset! b 2)))} "go")
                                 (el/span (str x "," y)))))
            {:keys [state] :as ctl} (render/render! (:container p) root (:d p))]
        (reset! runs 0)
        (.click (.querySelector (:container p) "button"))
        (is (= 1 @runs) "one root run")
        (is (= 2 (render/revision state)) "one commit, before the handler returned")
        (is (= "1,2" (.-textContent (.querySelector (:container p) "span"))))
        ((:unmount! ctl))
        (done)))))

;; ---------------------------------------------------------------------------
;; CB5: controlled inputs

(deftest cb5a-a-rejected-keystroke-is-reverted
  (with-world {}
    (fn [_ p done]
      (let [{:keys [input ctl]} (mount-input p (fn [_]))]
        (type! p input "12a")
        (is (= "12" (.-value input)) "before the handler returns")
        ((:unmount! ctl))
        (done)))))

(deftest cb5b-rejected-with-an-unrelated-commit
  (with-world {}
    (fn [_ p done]
      (let [{:keys [input state ctl]} (mount-input p #(swap! % inc))]
        (type! p input "12a")
        (is (= 2 (render/revision state)) "the unrelated commit lands")
        (is (= "1" (.-textContent (.querySelector (:container p) "span"))))
        (is (= "12" (.-value input)) "and the value is restored")
        ((:unmount! ctl))
        (done)))))

(deftest cb5c-accepted-but-deferred
  (with-world {:budget 8}
    (fn [_ p done]
      (let [t (v2/signal "12")
            mids (vec (for [i (range 40)] (spin (count (iv/get-new (track t))))))
            h (fn [e] (let [s (.. e -target -value)] (when (digits? s) (reset! t s))))
            root (spin (let [v (iv/get-new (track t))]
                         (loop [i 0 acc 0]
                           (if (< i (count mids))
                             (recur (inc i) (+ acc (v2/await (nth mids i))))
                             (el/div (el/input {:value v :on-input h}) (str acc))))))
            {:keys [state] :as ctl} (render/render! (:container p) root (:d p))]
        (render/on-revision state 1
                            (fn [_]
                              (later 0 (fn []
                                         (let [input (.querySelector (:container p) "input")
                                               r (render/revision state)]
                                           (type! p input "123")
                                           (is (= r (render/revision state)) "the commit has not landed: the check is withdrawn")
                                           (is (= "123" (.-value input)) "the typed value stays")
                                           (render/on-revision state (inc r)
                                                               (fn [_]
                                                                 (is (= "123" (.-value input)) "the later commit sets the same value")
                                                                 (later 0 (fn [] ((:unmount! ctl)) (done))))))))))))))

(deftest cb5d-a-rejected-checkbox-toggle-is-reverted
  (with-world {}
    (fn [_ p done]
      (let [c (v2/signal false)
            root (spin (el/div (el/input {:type "checkbox" :checked (iv/get-new (track c)) :on-change (fn [_] nil)})))
            ctl (render/render! (:container p) root (:d p))
            input (.querySelector (:container p) "input")]
        (set! (.-checked input) true)
        (fire! p input "change")
        (is (false? (.-checked input)))
        ((:unmount! ctl))
        (done)))))

(deftest cb5e-an-accepted-keystroke-is-not-touched
  (with-world {}
    (fn [_ p done]
      (let [{:keys [input state ctl]} (mount-input p (fn [_]))]
        (type! p input "123")
        (is (= 2 (render/revision state)) "one commit")
        (is (= "123" (.-value input)))
        ((:unmount! ctl))
        (done)))))

(deftest cb5f-a-non-inline-world-does-not-restore
  (with-world {:inline? false :budget 8}
    (fn [_ p done]
      (let [{:keys [state ctl] :as m} (mount-input p (fn [_]))]
        (render/on-revision state 1
                            (fn [_]
                              (let [input (.querySelector (:container p) "input")]
                                (later 0 (fn []
                                           (type! p input "12a")
                                           ;; the acknowledgement: a read queued behind the
                                           ;; handler's wait and withdrawal
                                           (v2/value-async (:root @state)
                                                           (fn [_ _]
                                                             (is (= "12a" (.-value input)) "the P4 scope: no asynchronous restore")
                                                             ((:unmount! ctl))
                                                             (done))))))))))))

(deftest cb5g-a-queued-callback-after-the-withdrawal
  (with-world {:budget 2}
    (fn [w p done]
      (let [{:keys [state ctl]} (mount-input p (fn [_]))
            ack (v2/signal 0)]
        (render/on-revision state 1
                            (fn [_]
                              (later 0 (fn []
                                         (let [input (.querySelector (:container p) "input")]
                                           ;; two items ahead of the handler's wait
                                           (dotimes [_ 2] (v2/send-world! w (fn [])))
                                           (type! p input "12a")
                                           (is (= "12a" (.-value input)) "no restore before the wrapper returned")
                                           (set! (.-value input) "999")
                                           ;; the acknowledgement: a callback queued behind the late one
                                           (v2/value-async ack
                                                           (fn [_ _]
                                                             (is (= "999" (.-value input)) "the late callback writes nothing")
                                                             ((:unmount! ctl))
                                                             (done))))))))))))

(deftest cb5h-the-callback-defers-to-a-flush-that-spills
  (async done*
         (let [done (fx/guard-done done*)
               hit (atom nil)
               try-budget
               (fn try-budget [budget]
                 (if (or @hit (> budget 12))
                   (do (is (some? @hit) "a budget at which the callback deferred and the flush came too late")
                       (done))
                   (let [w (v2/world {:budget budget :slice-ms nil})
                         p (page)
                         {:keys [state ctl u input]} (binding [v2/*world* w] (mount-input p (fn [_])))
                         deferred? (atom false)]
                     (render/on-revision state 1 (fn [_] (later 0 (fn []
                                                                    (v2/send-world! w #(reset! u 1))
                                                                    (add-watch state ::pending (fn [_ _ _ n] (when (seq (:restore-pending n)) (reset! deferred? true))))
                                                                    (type! p input "12a")
                                                                    (remove-watch state ::pending)
                                                                    (let [this? (and @deferred? (= "12a" (.-value input)))]
                                                                      (when this? (reset! hit budget))
                                  ;; the acknowledgement: a read queued behind the flush
                                                                      (v2/value-async (:root @state)
                                                                                      (fn [_ _]
                                                                                        (when this?
                                                                                          (is (= 2 (render/revision state)) "the flush commits")
                                                                                          (is (= "12a" (.-value input)) "but does not restore"))
                                                                                        ((:unmount! ctl))
                                                                                        (later 0 (fn []
                                                                                                   (v2/release-world! w)
                                                                                                   (try-budget (inc budget))))))))))))))]
           (try-budget 3))))

(deftest cb5i-liveness
  (testing "the handler unmounts the mount"
    (with-world {}
      (fn [_ p done]
        (let [ctl (volatile! nil)
              {:keys [input state] :as m} (mount-input p (fn [_] ((:unmount! @ctl))))]
          (vreset! ctl (:ctl m))
          (type! p input "12a")
          (is (= :unmounted (render/phase state)))
          (is (= "" (html p)) "no restore, no throw")
          (done))))))

(deftest cb5i-the-handler-removes-the-target
  (with-world {}
    (fn [_ p done]
      (let [show (v2/signal true)
            root (spin (let [sh (iv/get-new (track show))]
                         (el/div (when sh (el/input {:value "12" :on-input (fn [_] (reset! show false))})))))
            ctl (render/render! (:container p) root (:d p))
            input (.querySelector (:container p) "input")]
        (type! p input "12a")
        (is (= "<div></div>" (html p)))
        (is (= "12a" (.-value input)) "no restore on the removed element, no throw")
        ((:unmount! ctl))
        (done)))))

;; ---------------------------------------------------------------------------
;; Keyed fragment positions (sol's P4 review, finding 1)

(defn- keyed [fa ks items]
  (assoc (frag/keyed-fragment (vec items) nil) :addr fa :keys (vec ks)))

(defn- li [k] (el/li {:key k} (str k)))

(deftest an-empty-fragment-grows-at-its-slot
  (with-world {}
    (fn [_ p done]
      (let [ks (v2/signal [])
            root (spin (let [xs (iv/get-new (track ks))]
                         (el/div (el/h1 "head") (keyed :frag-a xs (mapv li xs)) (el/footer "foot"))))
            ctl (render/render! (:container p) root (:d p))]
        (reset! ks ["a"])
        (is (= "<div><h1>head</h1><li>a</li><footer>foot</footer></div>" (html p)))
        ((:unmount! ctl))
        (done)))))

(deftest a-fragment-grows-while-a-later-sibling-goes
  (with-world {}
    (fn [_ p done]
      (let [step (v2/signal 0)
            root (spin (let [s (iv/get-new (track step))
                             xs (if (zero? s) ["A"] ["A" "B"])]
                         (el/div (keyed :frag-b xs (mapv li xs)) (when (zero? s) (el/p "tail")))))
            ctl (render/render! (:container p) root (:d p))]
        (is (= "<div><li>A</li><p>tail</p></div>" (html p)))
        (reset! step 1)
        (is (= "<div><li>A</li><li>B</li></div>" (html p)))
        ((:unmount! ctl))
        (done)))))

;; ---------------------------------------------------------------------------
;; A select's value after its options (sol's P4 review, finding 6)

(deftest a-select-value-follows-its-new-option
  (with-world {}
    (fn [_ p done]
      (let [two? (v2/signal false)
            root (spin (let [t (iv/get-new (track two?))]
                         (el/div (el/select {:value (if t "b" "a")}
                                            (el/option {:value "a"} "a")
                                            (when t (el/option {:value "b"} "b"))))))
            ctl (render/render! (:container p) root (:d p))
            select (.querySelector (:container p) "select")]
        (is (= "a" (.-value select)))
        (reset! two? true)
        (is (= "b" (.-value select)) "the value is set after the option exists")
        ((:unmount! ctl))
        (done)))))

(defn- fragments-root [order]
  (spin (let [ns (iv/get-new (track order))]
          (el/div (mapv (fn [n] (keyed (keyword (str "frag-" n)) [n] [(el/li {:key n} n)])) ns)))))

(deftest fragments-swap-and-rotate-across-slots
  (with-world {}
    (fn [_ p done]
      (let [order (v2/signal ["F" "G" "H"])
            ctl (render/render! (:container p) (fragments-root order) (:d p))]
        (reset! order ["G" "F" "H"])
        (is (= "<div><li>G</li><li>F</li><li>H</li></div>" (html p)) "a swap")
        (reset! order ["F" "H" "G"])
        (is (= "<div><li>F</li><li>H</li><li>G</li></div>" (html p)) "a rotation")
        ((:unmount! ctl))
        (done)))))
