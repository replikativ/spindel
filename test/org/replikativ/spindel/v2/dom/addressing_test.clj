(ns org.replikativ.spindel.v2.dom.addressing-test
  "DOM addressing (A3) on the JVM (phase-d design §2.3-§2.6, §2.10: D3-D8,
   and sol's cases): element macros pass the address in the reserved locals
   `__dom-parent`/`__dom-slot`, plain components read the synchronous
   context, computations capture the address as an input."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [clojure.string :as str]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await await-all]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.dom.addressing :as addr]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.verify :as verify]
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
;; D3: plain components in an effect-free child, a hoisted call, a `let`
;; initializer (sol T8) and a `let` tail

(deftest d3-plain-components-get-their-slot
  (let [d (v2/deferred)
        c (spin (el/ul (card "a")
                       (card (await d))
                       (let [u (await d) node (card u)] node)
                       (let [u (await d)] (card u))
                       (when (await d) (card "w"))
                       (do (await d) (card "d"))))
        u (v2/observe! c (fn [_ _]))]
    (v2/deliver! d "v")
    (let [vn (now c) ul (:addr vn)]
      (is (= (mapv #(card-at ul %) (range 6)) (mapv :addr (:children vn))))
      (is (not= (card-at nil nil) (:addr (first (:children vn)))) "not rooted at nil"))
    (u)))

;; ---------------------------------------------------------------------------
;; D4: an inline spin captures the address; moved to another slot, it reruns

(defn- boxed
  "A plain component with an inline computation; records its handle."
  [runs made]
  (el/div (let [h (spin (swap! runs inc) (el/span "in"))]
            (swap! made conj h)
            h)))

(defn- boxed-span-at
  "The address of `boxed`'s inner span when `boxed` is at `p`, `s`."
  [p s]
  (let [made (atom [])]
    (addr/call-with-context p s #(boxed (atom 0) made))
    (:addr (now (peek @made)))))

(deftest d4-inline-spin-captures-its-address
  (let [flag (v2/signal true)
        tick (v2/signal 0)
        runs (atom 0)
        made (atom [])
        c (spin (let [f (iv/get-new (track flag))
                      _ (track tick)]
                  (el/section (if f (boxed runs made) nil)
                              (if f nil (boxed runs made)))))
        u (v2/observe! c (fn [_ _]))
        sec (:addr (now c))]
    (is (= (boxed-span-at sec 0) (:addr (now (peek @made)))))
    (is (= 1 @runs))
    (v2/write! tick 1)
    (now c)
    (is (= (boxed-span-at sec 0) (:addr (now (peek @made)))))
    (is (= 1 @runs) "adopted at the same slot: no rerun")
    (v2/write! flag false)
    (now c)
    (is (= (boxed-span-at sec 1) (:addr (now (peek @made)))))
    (is (= 2 @runs) "adopted at another slot: its captured address changed, it reruns")
    (is (= 1 (count (set (map rid @made)))) "one computation throughout")
    (u)))

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
;; D6: `el/in-context` after a suspension inside `case` and `loop`; the
;; compile-time warning for those forms (and `try`) without it

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

(defn- compile-warnings
  "What compiling `form` in this namespace prints to *err*."
  [form]
  (reset! @#'el/warned #{})
  (let [w (java.io.StringWriter.)]
    (binding [*err* w
              *ns* (the-ns 'org.replikativ.spindel.v2.dom.addressing-test)]
      (eval form))
    (str w)))

(deftest d6-unaddressed-call-warning
  (testing "an effectful case, try or loop with a plain component call warns"
    (doseq [form ['(fn [m] (spin (el/div (case (await m) :a (card "a") nil))))
                  '(fn [m] (spin (el/div (try (await m) (card "t") (catch Exception _ nil)))))
                  '(fn [m] (spin (el/div (loop [i 0] (if (< i 2) (do (await m) (recur (inc i))) (card i))))))]]
      (let [out (compile-warnings form)]
        (is (str/includes? out ":org.replikativ.spindel.v2.dom.elements/unaddressed-call") (pr-str form))
        (is (str/includes? out (str ":line " (:line (meta form)))) "names the location"))))
  (testing "no warning with el/in-context, or for the handled shapes"
    (doseq [form ['(fn [m] (spin (el/div (case (await m) :a (el/in-context (card "a")) nil))))
                  '(fn [m] (spin (el/div (try (await m) (el/in-context (card "t")) (catch Exception _ nil)))))
                  '(fn [m] (spin (el/div (loop [i 0] (if (< i 2) (do (await m) (recur (inc i))) (el/in-context (card i)))))))
                  '(fn [m] (spin (el/div (let [u (await m) node (card u)] node) (card (await m)))))
                  '(fn [m] (spin (el/div (case (await m) :a (el/span "plain") nil))))]]
      (is (= "" (compile-warnings form)) (pr-str form)))))

;; ---------------------------------------------------------------------------
;; D7: `effectful?` is scope-aware

(v2/defeffect probe-effect [_ _] [:value 1])

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
        (is (not (e? '(letfn [(f [] (await x))] (f))))))
      (testing "a local named like an effect shadows it"
        (is (not (e? '(let [await identity] (await x)))))
        (is (not (e? '(loop [await identity] (await x)))))
        (is (not (e? '{await true} '(await x))))
        (is (not (e? '(let [probe-effect identity] (probe-effect 1)))))
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
  "A plain component that creates a computation without el/component."
  [kept]
  (reset! kept (spin :child))
  (el/span "s"))

(deftest d8-child-does-not-retain-the-creator-run
  (let [w v2/*world*
        flag (v2/signal true)
        kept (atom nil)
        run (atom nil)
        c (spin (let [f (iv/get-new (track flag))]
                  (when-not @run (reset! run (java.lang.ref.WeakReference. (v2/active-run))))
                  (el/div (when f (spawner kept)))))
        u (v2/observe! c (fn [_ _]))]
    (now c)
    (is (= :child (now @kept)))
    (v2/write! flag false)
    (now c)
    (verify/gc-settle! w)
    (is (= :child (now @kept)) "the child is still retained")
    (is (nil? (.get ^java.lang.ref.WeakReference @run)) "its creator's retired run is not")
    (u)))

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
