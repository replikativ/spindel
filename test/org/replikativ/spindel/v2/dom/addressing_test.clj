(ns org.replikativ.spindel.v2.dom.addressing-test
  "DOM addressing (A3), the JVM-only cases (phase-d design §2.3-§2.6,
   §2.10: D5-D8, and sol's cases); the portable ones are in
   addressing-cljc-test. Element macros pass the address in the reserved
   locals `__dom-parent`/`__dom-slot`, plain components read the
   synchronous context, computations capture the address as an input."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await await-all]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.dom.addressing :as addr]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture]]
            [org.replikativ.spindel.incremental.interval :as iv]))

(use-fixtures :each checked-fixture)

(defn- now [h] (v2/value h 2000 ::timeout))

(defn- rid [h] (v2/call-in! v2/*world* #(aget ^objects (v2/row-of h) rw/ID)))

(defn card
  "A plain component."
  [x]
  (el/li {:class "card"} (el/span x)))

(defn- card-at
  "The address `card` has at parent `p`, slot `s`."
  [p s]
  (:addr (addr/call-with-context p s #(card "z"))))

;; ---------------------------------------------------------------------------
;; D5: `el/component` captures the address; called at two slots, two
;; computations. Also sol's awaited component call in a `let` initializer.

(defn- card-c
  "A component computation; records its handle."
  [x made]
  (let [h (el/component (el/li {:class "c"} (el/span x)))]
    (swap! made conj h)
    h))

(deftest d5-component-captures-its-address
  (let [made (atom [])
        c (spin (el/ul (await (card-c "a" made))
                       (await (card-c "b" made))
                       (let [node (await (card-c "q" made))] node)))
        vn (now c)
        ul (:addr vn)
        expected (fn [s] (:addr (now (addr/call-with-context ul s #(card-c "z" (atom []))))))]
    (is (= (mapv expected (range 3)) (mapv :addr (:children vn))))
    (is (= 3 (count (set (map rid @made)))) "one computation per call")
    (is (not= (expected 0) (:addr (now (card-c "z" (atom []))))) "outside a context it is rooted at nil")))

;; ---------------------------------------------------------------------------
;; D6: `el/in-context` after a suspension inside `case` and `loop` (the
;; warnings are in addressing-cljc-test); an effect in its body is a compile
;; error

(deftest d6-in-context-after-suspension
  (let [mode (v2/deferred)
        d (v2/deferred)
        c (spin (el/div (case (await mode) :a (el/in-context (card "a")) nil)
                        (loop [i 0]
                          (if (< i 2)
                            (do (await d) (recur (inc i)))
                            (el/in-context (card i))))))
        u (v2/observe! c (fn [_ _]))]
    (v2/deliver! mode :a)
    (v2/deliver! d true)
    (let [vn (now c) div (:addr vn)]
      (is (= [(card-at div 0) (card-at div 1)] (mapv :addr (:children vn)))))
    (u)))

(defn- compile-error
  "The message of the error compiling `form` in this namespace throws, or nil."
  [form]
  (binding [*ns* (the-ns 'org.replikativ.spindel.v2.dom.addressing-test)]
    (try (eval form) nil
         (catch Throwable t (str (ex-message t) " " (some-> (ex-cause t) ex-message))))))

(deftest in-context-rejects-an-effect
  (is (re-find #"in-context" (str (compile-error '(fn [d] (spin (el/div (el/in-context (await d))))))))))

(deftest caller-evaluated-operands-may-suspend
  (testing "an await in aseq's initializer or task-with's options of a child that calls a component"
    (is (nil? (compile-error '(fn [d] (spin (el/div (card (v2/aseq [s (await d)] nil))))))))
    (is (nil? (compile-error '(fn [d] (spin (el/div (card (v2/task-with {:x (await d)} 1))))))))))

;; ---------------------------------------------------------------------------
;; D7: `effectful?` is scope-aware

(v2/defeffect probe-effect [_ _] [:value 1])

(defmacro my-spin [& body] `(spin ~@body))

(deftest d7-effectful?
  (binding [*ns* (the-ns 'org.replikativ.spindel.v2.dom.addressing-test)]
    (let [e? (fn ([f] (v2/effectful? {} f)) ([env f] (v2/effectful? env f)))]
      (testing "effects in the execution scope"
        (is (e? '(await x)))
        (is (e? '(v2/track x)))
        (is (e? '(str "a" (await x))))
        (is (e? '(when c (await x))))
        (is (e? '(let [y (await x)] y)))
        (is (e? '(probe-effect 1)) "a defeffect effect")
        (is (e? '(letfn [(f [] 1)] (await (f)))) "a letfn body")
        (is (e? '(el/div (await x))) "a DOM macro's children"))
      (testing "not inside nested bodies, closures or quotes"
        (is (not (e? '(spin (await x)))))
        (is (not (e? '(task (await x)))))
        (is (not (e? '(v2/task-with {} (await x)))))
        (is (not (e? '(v2/aseq [s 0] (await x)))))
        (is (not (e? '(card (spin (await x))))))
        (is (not (e? '(el/component (await x)))))
        (is (not (e? ''(await x))))
        (is (not (e? '(fn [] (await x)))))
        (is (not (e? '(letfn [(f [] (await x))] (f)))))
        (is (not (e? '(my-spin (await x)))) "a user macro expanding to spin"))
      (testing "caller-evaluated operands of the body forms"
        (is (e? '(v2/aseq [s (await d)] nil)) "aseq's initializer")
        (is (e? '(v2/task-with {:x (await d)} 1)) "task-with's options")
        (is (not (e? '(v2/aseq [s 0] (await x)))))
        (is (not (e? '(v2/task-with {} (await x))))))
      (testing "destructuring defaults are evaluated in scope"
        (is (e? '(let [{:keys [a] :or {a (await x)}} m] a))))
      (testing "a local named like an effect shadows it"
        (is (not (e? '(let [await identity] (await x)))))
        (is (not (e? '(loop [await identity] (await x)))))
        (is (not (e? '{await true} '(await x))))
        (is (not (e? '(let [probe-effect identity] (probe-effect 1)))))
        (is (not (e? '(letfn [(await [y] y)] (await x)))) "a letfn name")
        (is (e? '(let [await identity] (track x))))))))

;; ---------------------------------------------------------------------------
;; D8 (JVM): the lifetime token

(deftest d8-conveyed-future-sees-no-context
  (testing "a future derefed during the call: another thread"
    (is (= [nil nil] (addr/call-with-context :p 1 #(deref (future (addr/current)) 1000 ::timeout)))))
  (testing "a future that reads after the call returned: a dead token"
    (let [gate (promise)
          f (addr/call-with-context :p 1 #(future @gate (addr/current)))]
      (deliver gate true)
      (is (= [nil nil] (deref f 1000 ::timeout))))))

(defn- spawner
  "A plain component that creates a computation without el/component; the
   computation reports the context its body sees."
  [kept]
  (reset! kept (spin (let [c addr/*context*]
                       [(set (keys c)) (some-> c :live deref) (vec (vals c))])))
  (el/span "s"))

(deftest d8-child-frame-holds-no-run
  ;; the child's body runs on the binding frame conveyed from the component
  ;; call: the context it sees there is the dead record, holding no run
  (let [kept (atom nil)
        run (atom nil)
        c (spin (reset! run (v2/active-run))
                (el/div (spawner kept)))
        _ (now c)
        [fields live values] (now @kept)]
    (is (= #{:parent :slot :live} fields) "the record has no other field")
    (is (nil? live) "its token is dead")
    (is (not-any? #(identical? @run %) values) "and it holds no run")))

;; ---------------------------------------------------------------------------
;; sol: two helper call sites with overlapping keys keep their own
;; computations (generated spins carry the caller's site)

(defn- helper-a [runs ks]
  (loop [ks ks acc []]
    (if-let [k (first ks)]
      (recur (rest ks)
             (conj acc (v2/with-key k (el/component (swap! runs update [:a k] (fnil inc 0))
                                                    (el/li (str "a" k))))))
      acc)))

(defn- helper-b [runs ks]
  (loop [ks ks acc []]
    (if-let [k (first ks)]
      (recur (rest ks)
             (conj acc (v2/with-key k (el/component (swap! runs update [:b k] (fnil inc 0))
                                                    (el/li (str "b" k))))))
      acc)))

(deftest helper-sites-with-overlapping-keys
  (let [order (v2/signal true)
        runs (atom {})
        texts (fn [vns] (mapv #(get-in % [:children 0 :content]) vns))
        c (spin (let [a-first (iv/get-new (track order))
                      hs (el/in-context
                          (if a-first
                            (into (helper-a runs [1 2]) (helper-b runs [2 3]))
                            (into (helper-b runs [2 3]) (helper-a runs [1 2]))))]
                  (await-all hs)))
        u (v2/observe! c (fn [_ _]))]
    (is (= ["a1" "a2" "b2" "b3"] (texts (now c))))
    (v2/write! order false)
    (is (= ["b2" "b3" "a1" "a2"] (texts (now c))))
    (is (= {[:a 1] 1 [:a 2] 1 [:b 2] 1 [:b 3] 1} @runs) "every computation was readopted by its own site")
    (u)))

(defn- helper [tag runs ks]
  (loop [ks ks acc []]
    (if-let [k (first ks)]
      (recur (rest ks)
             (conj acc (v2/with-key k (el/component (swap! runs update [tag k] (fnil inc 0))
                                                    (el/li (str (name tag) k))))))
      acc)))

(deftest one-helper-twice-with-overlapping-keys
  (testing "positional: the values stay right, the swapped invocations rerun"
    (let [order (v2/signal true)
          runs (atom {})
          texts (fn [vns] (mapv #(get-in % [:children 0 :content]) vns))
          c (spin (let [a-first (iv/get-new (track order))
                        hs (el/in-context
                            (if a-first
                              (into (helper :a runs [1 2]) (helper :b runs [2 3]))
                              (into (helper :b runs [2 3]) (helper :a runs [1 2]))))]
                    (await-all hs)))
          u (v2/observe! c (fn [_ _]))]
      (is (= ["a1" "a2" "b2" "b3"] (texts (now c))))
      (v2/write! order false)
      (is (= ["b2" "b3" "a1" "a2"] (texts (now c))))
      (u)))
  (testing "keyed by the caller: every computation keeps its identity"
    (let [order (v2/signal true)
          runs (atom {})
          texts (fn [vns] (mapv #(get-in % [:children 0 :content]) vns))
          c (spin (let [a-first (iv/get-new (track order))
                        a #(v2/with-key :a (helper :a runs [1 2]))
                        b #(v2/with-key :b (helper :b runs [2 3]))
                        hs (el/in-context (if a-first (into (a) (b)) (into (b) (a))))]
                    (await-all hs)))
          u (v2/observe! c (fn [_ _]))]
      (is (= ["a1" "a2" "b2" "b3"] (texts (now c))))
      (v2/write! order false)
      (is (= ["b2" "b3" "a1" "a2"] (texts (now c))))
      (is (= {[:a 1] 1 [:a 2] 1 [:b 2] 1 [:b 3] 1} @runs) "no reruns")
      (u))))
