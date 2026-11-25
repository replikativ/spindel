(ns org.replikativ.spindel.v2.dom.addressing-cljc-test
  "DOM addressing (A3) on both platforms (phase-d design §2.10: D1, D2, D8):
   element addresses travel in lexical locals across suspension, are the
   same keywords on the JVM and on Node, and a plain component's
   synchronous context is valid only within its call."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing async]])
            [clojure.string :as str]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.addressing :as addr]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.addressing-fixture :as fx]
            #?(:clj [org.replikativ.spindel.v2.verify :as verify]))
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.dom.addressing-cljc-test :refer [static+awaited warnings-of]])))

#?(:clj
   (defn- subst
     "`form` with every `hole` replaced by `x`, keeping each form's metadata
      (so element forms keep their source locations)."
     [form hole x]
     (cond (= form hole) x
           (seq? form) (with-meta (apply list (map #(subst % hole x) form)) (meta form))
           (vector? form) (with-meta (mapv #(subst % hole x) form) (meta form))
           (map? form) (with-meta (into {} (map (fn [[k v]] [(subst k hole x) (subst v hole x)])) form)
                         (meta form))
           :else form)))

#?(:clj
   (defmacro static+awaited
     "From one tree form: [the tree with `hole` replaced by `v`, evaluated
      here; a computation of the tree with `hole` replaced by (await d)].
      Both have the same source locations."
     [hole v d tree]
     [(subst tree hole v) `(spin ~(subst tree hole `(await ~d)))]))

#?(:clj
   (defmacro warnings-of
     "What compiling `form` here prints to *err* (the element macros'
      compile-time warnings), as a string; a compile error as \"THREW msg\"."
     [form]
     (reset! @(resolve 'org.replikativ.spindel.v2.dom.elements/warned) #{})
     (let [w (java.io.StringWriter.)]
       (binding [*err* w]
         (try (if (:js-globals &env)
                ((requiring-resolve 'cljs.analyzer/analyze) &env form)
                (eval form))
              (catch Throwable t (.write w (str "THREW " (.getMessage t))))))
       (str w))))

(defn- then
  "Calls `(k v)` with `h`'s settled value (`[:err e]` for an error)."
  [h k]
  #?(:clj (k (try (v2/value h 2000 ::timeout) (catch Exception e [:err e])))
     :cljs (v2/value-async h (fn [v err?] (k (if err? [:err v] v))))))

(defn- later
  "Runs `f` off the current synchronous extent: a JVM future, a JS timer."
  [f]
  #?(:clj (future (Thread/sleep 20) (f))
     :cljs (js/setTimeout f 20)))

(defn- in-world
  "Runs `(f done)` with a fresh world bound; the test ends at `(done)`."
  [f]
  #?(:clj (let [acc (atom [])
                w (v2/world {:verify? true :hook (verify/checking-hook acc)})
                p (promise)]
            (try (binding [v2/*world* w] (f #(deliver p true)))
                 (is (true? (deref p 5000 false)) "the test completes")
                 (finally (v2/release-world! w)))
            (is (empty? @acc) (str "Rule R divergences: " (vec (take 3 @acc)))))
     :cljs (async done
                  (let [w (v2/world)]
                    (binding [v2/*world* w]
                      (f (fn [] (v2/release-world! w) (js/setTimeout done 0))))))))

(defn- addrs
  "Pre-order [tag address] of the element nodes of vnode `n`."
  [n]
  (if (and (map? n) (:addr n))
    (into [[(:tag n) (:addr n)]] (mapcat addrs (:children n)))
    []))

;; ---------------------------------------------------------------------------
;; D1: nested elements around an await

(deftest d1-addresses-survive-suspension
  (in-world
   (fn [done]
     (let [d (v2/deferred)
           [static c] (static+awaited
                       HOLE "v" d
                       (el/div {:class "a"}
                               (el/span HOLE)
                               (el/ul (el/li "x")
                                      (el/li (let [u HOLE] (el/b u)))
                                      (el/li {:key HOLE} (el/i "k")))
                               (el/p (str "p" HOLE))))
           u (v2/observe! c (fn [_ _]))]
       (later #(v2/deliver! d "v"))
       (then c (fn [vn]
                 (is (= (addrs static) (addrs vn)) "the awaited tree has the static tree's addresses")
                 (is (= 9 (count (addrs vn))))
                 (is (apply distinct? (map second (addrs vn))))
                 (is (= "v" (get-in vn [:children 0 :children 0 :content])))
                 (u) (done)))))))

;; ---------------------------------------------------------------------------
;; D2: the same static tree, the same keywords on every platform

(def ^:private d2-expected
  ;; generated on the JVM from addressing-fixture/tree; Node must agree
  [[:div :el-1668504a-c61a-5bd2-8050-b30ec27309db]
   [:span :el-1ba67d83-54c4-52df-a4b8-32183fb58a6d]
   [:ul :el-295ef1b2-32ce-5686-ba56-c2ebb39dd0ff]
   [:li :keyed-2d69bf6e-2cfd-58ea-80d0-31b9b2a179bc]
   [:li :el-176260a0-29b5-582d-b488-fd28a6f14d38]
   [:li :el-202cbdc2-828c-5e8d-9f90-8274717f0115]
   [:span :el-303bd29c-b3cf-510d-abcd-635de2457ec2]])

(deftest d2-same-addresses-on-every-platform
  (is (= d2-expected (addrs (fx/tree)))))

;; ---------------------------------------------------------------------------
;; D8: the synchronous context lives only within its call

(deftest d8-context-within-the-call-only
  (testing "valid inside, absent after"
    (is (= [:p 3] (addr/call-with-context :p 3 addr/current)))
    (is (= [nil nil] (addr/current))))
  (testing "a callback made inside and called after the call returns"
    (let [cb (addr/call-with-context :p 3 #(#?(:clj bound-fn* :cljs identity) addr/current))]
      (is (= [nil nil] (cb)))))
  (testing "nested calls restore the outer context"
    (is (= [[:q 1] [:p 3]]
           (addr/call-with-context :p 3 (fn [] [(addr/call-with-context :q 1 addr/current) (addr/current)]))))))

(defn- probe
  "A plain component: records its context during the call and, from a
   future or a timer started in the call, after it."
  [seen]
  (swap! seen assoc :in-call (addr/current))
  (later #(swap! seen assoc :later (addr/current)))
  (el/span "probe"))

(defn- when-seen
  "Calls `k` once `seen` has a :later entry, or after about two seconds
   (the assertions then fail)."
  ([seen k] (when-seen seen k 200))
  ([seen k tries]
   (if (or (contains? @seen :later) (zero? tries))
     (k)
     #?(:clj (do (Thread/sleep 10) (recur seen k (dec tries)))
        :cljs (js/setTimeout #(when-seen seen k (dec tries)) 10)))))

(deftest d8-deferred-reads-see-no-context
  (in-world
   (fn [done]
     (let [seen (atom {})
           c (spin (el/div (el/b "x") (probe seen)))]
       (then c (fn [vn]
                 (is (= [(:addr vn) 1] (:in-call @seen)) "the component's root is the div's slot 1")
                 (when-seen seen
                            (fn []
                              (is (= [nil nil] (:later @seen)) "a future or a timer started in the call sees none")
                              (done)))))))))

;; ---------------------------------------------------------------------------
;; Plain components at every supported position (D3), on both platforms

(defn card
  "A plain component."
  [x]
  (el/li {:class "card"} (el/span x)))

(defn- card-at
  "The address `card` has at parent `p`, slot `s`."
  [p s]
  (:addr (addr/call-with-context p s #(card "z"))))

(deftest d3-plain-components-get-their-slot
  (in-world
   (fn [done]
     (let [d (v2/deferred)
           saved (atom nil)
           c (spin (el/ul (card "a")                                    ; effect-free child
                          (card (await d))                              ; hoisted call
                          (let [u (await d) node (card u)] node)        ; let initializer (sol T8)
                          (let [u (await d)] (card u))                  ; let tail
                          (when (await d) (card "w"))                   ; when branch
                          (do (await d) (card "d"))                     ; do tail
                          (do (await d) (reset! saved (card "x")) @saved)  ; a non-final do form
                          (let [{:keys [node] :or {node (card (await d))}} {}] node) ; a destructuring default
                          (if (some? (reset! saved (card (await d)))) @saved nil)    ; an if test
                          (let [u (await d) _ (card u)] (card u))       ; a non-final binding
                          (apply card [(await d)])                      ; an indirect call, hoisted
                          (apply card ["x"])                            ; an indirect call
                          (first (mapv card ["x"]))                     ; an indirect eager call
                          (first (mapv (fn [x] (card x)) ["x"]))))      ; through a closure
           u (v2/observe! c (fn [_ _]))]
       (later #(v2/deliver! d "v"))
       (then c (fn [vn]
                 (let [ul (:addr vn)]
                   (is (= (mapv #(card-at ul %) (range 14)) (mapv :addr (:children vn))))
                   (is (not= (card-at nil nil) (:addr (first (:children vn)))) "not rooted at nil"))
                 (u) (done)))))))

;; ---------------------------------------------------------------------------
;; Computations: an inline spin and el/component capture the address and
;; rerun when moved (D4); a component computation that delegates to a
;; plain component (sol P1); components in caller-evaluated operands of
;; aseq and task-with (sol P1)

(defn wrapped-card
  "A component computation delegating to a plain component."
  [x]
  (el/component (card x)))

(defn awaiting-card
  "A component computation delegating after a suspension."
  [d x]
  (el/component (let [u (await d)] (card (str x u)))))

(deftest component-delegating-to-a-plain-component
  (in-world
   (fn [done]
     (let [d (v2/deferred)
           c (spin (el/ul (await (wrapped-card "a"))
                          (await (wrapped-card "b"))
                          (await (awaiting-card d "c"))
                          (el/div (await (spin (card "s"))))))
           u (v2/observe! c (fn [_ _]))]
       (later #(v2/deliver! d "v"))
       (then c (fn [vn]
                 (let [ul (:addr vn) [a b cc div] (:children vn)]
                   (is (= [(card-at ul 0) (card-at ul 1) (card-at ul 2)] (mapv :addr [a b cc])))
                   (is (= (card-at (:addr div) 0) (get-in div [:children 0 :addr])) "an inline spin delegating"))
                 (u) (done)))))))

(defn- boxed
  "A plain component with an inline computation; records its handle."
  [runs made]
  (el/div (let [h (spin (swap! runs inc) (el/span "in"))]
            (swap! made conj h)
            h)))

(deftest d4-inline-spin-moves-and-reruns
  (in-world
   (fn [done]
     (let [flag (v2/signal true)
           tick (v2/signal 0)
           runs (atom 0)
           made (atom [])
           c (spin (let [f (iv/get-new (track flag))
                         _ (track tick)]
                     (el/section (if f (boxed runs made) nil)
                                 (if f nil (boxed runs made)))))
           u (v2/observe! c (fn [_ _]))
           span-of (fn [k] (then (peek @made) #(k (:addr %))))]
       (then c (fn [vn]
                 (span-of
                  (fn [a0]
                    (is (= 1 @runs))
                    (v2/write! tick 1)
                    (then c (fn [_]
                              (span-of
                               (fn [a0']
                                 (is (= a0 a0'))
                                 (is (= 1 @runs) "adopted at the same slot: no rerun")
                                 (v2/write! flag false)
                                 (then c (fn [vn']
                                           (is (= (:addr vn) (:addr vn')))
                                           (span-of
                                            (fn [a1]
                                              (is (not= a0 a1))
                                              (is (= 2 @runs) "moved to another slot: it reruns")
                                              (u) (done)))))))))))))))))

(defn- probe-ctx
  "Records the synchronous context it is called in; returns `v`."
  [seen v]
  (swap! seen conj (addr/current))
  v)

(deftest components-in-caller-evaluated-operands
  (in-world
   (fn [done]
     (let [seen (atom [])
           c (spin (el/div (do (v2/aseq [s (probe-ctx seen 0)] nil)
                               (v2/task-with (probe-ctx seen {}) :t)
                               (el/b "x"))))]
       (then c (fn [vn]
                 (is (= [[(:addr vn) 0] [(:addr vn) 0]] @seen))
                 (done)))))))

;; ---------------------------------------------------------------------------
;; The compile-time warning (D6, and sol P2-P4)

(deftest unaddressed-call-warnings
  (testing "unsupported effectful forms that call a plain component"
    (doseq [[label out] [[:case (warnings-of (fn [m] (spin (el/div (case (await m) :a (card "a") nil)))))]
                         [:try (warnings-of (fn [m] (spin (el/div (try (await m) (card "t") (catch #?(:clj Exception :cljs :default) _ nil))))))]
                         [:loop (warnings-of (fn [m] (spin (el/div (loop [i 0] (if (< i 2) (do (await m) (recur (inc i))) (card i)))))))]
                         [:lazy (warnings-of (fn [] (spin (el/div (map card ["x"])))))]
                         [:for (warnings-of (fn [] (spin (el/div (for [x ["x"]] (card x))))))]
                         [:task (warnings-of (fn [] (spin (el/div (let [t (task (card "x"))] nil)))))]
                         [:nested-spin (warnings-of (fn [] (spin (el/div (cond true (spin (card "x")))))))]]]
      (is (str/includes? out ":org.replikativ.spindel.v2.dom.elements/unaddressed-call") (str label " " out))
      (is (not (str/includes? out "THREW")) (str label " " out))))
  (testing "no warning with el/in-context, or for the handled shapes"
    (doseq [[label out] [[:case (warnings-of (fn [m] (spin (el/div (case (await m) :a (el/in-context (card "a")) nil)))))]
                         [:loop (warnings-of (fn [m] (spin (el/div (loop [i 0] (if (< i 2) (do (await m) (recur (inc i))) (el/in-context (card i))))))))]
                         [:let (warnings-of (fn [m] (spin (el/div (let [u (await m) node (card u)] node) (card (await m))))))]
                         [:do (warnings-of (fn [m s] (spin (el/div (do (await m) (reset! s (card "x")) @s)))))]
                         [:eager (warnings-of (fn [] (spin (el/div (mapv card ["x"])))))]
                         [:plain (warnings-of (fn [m] (spin (el/div (case (await m) :a (el/span "plain") nil)))))]
                         [:spin (warnings-of (fn [] (spin (el/div (spin (card "x"))))))]
                         [:component (warnings-of (fn [] (el/component (card "x"))))]]]
      (is (= "" out) (str label " " out)))))

;; ---------------------------------------------------------------------------
;; D8: the token on an exceptional exit

(deftest d8-exceptional-exit
  (let [cb (atom nil)
        thrown (try (addr/call-with-context :p 1 (fn []
                                                   (reset! cb (#?(:clj bound-fn* :cljs identity) addr/current))
                                                   (throw (ex-info "boom" {}))))
                    (catch #?(:clj Exception :cljs :default) e (ex-message e)))]
    (is (= "boom" thrown))
    (is (= [nil nil] (addr/current)) "the binding is restored")
    (is (= [nil nil] (@cb)) "the token is dead"))
  (is (= [:p 1] (addr/call-with-context :p 1
                                        (fn []
                                          (try (addr/call-with-context :q 2 #(throw (ex-info "inner" {})))
                                               (catch #?(:clj Exception :cljs :default) _ nil))
                                          (addr/current))))
      "an inner call that throws restores the outer context"))

;; ---------------------------------------------------------------------------
;; Hoisting keeps the operands' evaluation order (sol's second P4a review):
;; a var read stays before a later operand that mutates or suspends

(def table {:k "old"})

(defn- replace-table! [v]
  #?(:clj (alter-var-root #'table (constantly v))
     :cljs (set! table v)))

(deftest hoisting-reads-a-var-in-order
  (replace-table! {:k "old"})
  (in-world
   (fn [done]
     (let [d (v2/deferred)
           c (spin (el/div (get table (do (replace-table! {:k "new"}) (await d)))))]
       (later #(v2/deliver! d :k))
       (then c (fn [vn]
                 (is (= "old" (get-in vn [:children 0 :content])) "table is read before the mutation")
                 (replace-table! {:k "old"})
                 (done)))))))

(defn- note!
  "Records `x` in `log`; returns it."
  [log x]
  (swap! log conj x)
  x)

(deftest hoisting-keeps-the-operand-order
  (replace-table! {:k "old"})
  (in-world
   (fn [done]
     (let [d (v2/deferred)
           log (atom [])
           out (atom nil)
           c (spin (let [x :local]
                     (el/div (reset! out (vector (note! log 1)
                                                 table
                                                 x
                                                 (do (replace-table! {:k "new"}) (note! log 2) (await d))
                                                 (note! log 3)
                                                 table
                                                 (note! log 4))))))]
       (later #(v2/deliver! d :awaited))
       (then c (fn [_]
                 (is (= [1 2 3 4] @log) "side effects in operand order")
                 (is (= [1 {:k "old"} :local :awaited 3 {:k "new"} 4] @out) "each var read where it was written")
                 (replace-table! {:k "old"})
                 (done)))))))
