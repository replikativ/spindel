(ns org.replikativ.spindel.v2.dom.foreach-test
  "`ifor-each` on engine v2 (phase-d design §4.3): one computation per item,
   created under `(with-key fa)` and `(with-key k)`, so a later run adopts
   each item by its key and only an item whose captures changed reruns. The
   items sit at keyed addresses under the fragment's address; keys are
   checked (nil, false and duplicates throw); a render fn that returns a
   computation is awaited; a literal render fn may track and await."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track await]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.addressing :as addr]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.foreach :refer [ifor-each]]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx])
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.dom.foreach-test :refer [tagged-list]])))

(defn- dom [env] (mock/dom (:discharge (:mock env)) :container))

(defn- ops [env] @(:log (:mock env)))

(defn- clear-ops! [env] (reset! (:log (:mock env)) []))

(defn- created [env] (filterv #(= :create-element (:op %)) (ops env)))

(defn- delta
  "The runs since `before`, keys with no run left out."
  [runs before]
  (into {} (keep (fn [[k n]] (let [d (- n (get before k 0))] (when (pos? d) [k d])))) runs))

(defn- row
  "A plain component: an item row."
  [x]
  (el/li {:class "row"} (:v x)))

(defn- lis [vs] (mapv (fn [v] [:li {:class "row"} v]) vs))

(deftest a-keyed-list-adopts-its-items
  (fx/each-world
   (fn [env]
     (let [a {:id 1 :v "a"} b {:id 2 :v "b"} c {:id 3 :v "c"}
           items (v2/signal [a b])
           runs (atom {})
           root (spin (el/ul (ifor-each :id (track items)
                                        (fn [x] (swap! runs update (:id x) (fnil inc 0)) (row x)))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (is (= [(into [:ul {}] (lis ["a" "b"]))] (dom env)))
       (is (= {1 1 2 1} @runs))
       (let [fragment (first (:slots (render/committed state)))
             [la lb] (:children (render/committed state))]
         (is (= [1 2] (:keys (:value fragment))) "the fragment carries the item keys")
         (is (some? (:addr (:value fragment))))
         (is (not= (:addr la) (:addr lb)) "each item's root has its own address"))
       (testing "reverse: no item runs, no element created, the same item addresses"
         (let [before @runs
               addrs-before (set (map :addr (:children (render/committed state))))]
           (clear-ops! env)
           (fx/write! env items [b a])
           (is (= [(into [:ul {}] (lis ["b" "a"]))] (dom env)))
           (is (= {} (delta @runs before)))
           (is (empty? (created env)))
           (is (= addrs-before (set (map :addr (:children (render/committed state))))))))
       (testing "insert at the head: one item runs, one li is created"
         (let [before @runs]
           (clear-ops! env)
           (fx/write! env items [c b a])
           (is (= [(into [:ul {}] (lis ["c" "b" "a"]))] (dom env)))
           (is (= {3 1} (delta @runs before)))
           (is (= [:li] (mapv :tag (created env))))))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

(defn- error-of
  "The ex-data :type of `h`'s error result, or ::none."
  [env h]
  (try (fx/read! env h) ::none
       (catch #?(:clj Exception :cljs :default) e (:type (ex-data e)))))

(deftest keys-are-checked
  (fx/each-world
   (fn [env]
     (let [xs (v2/signal [{:id 1} {:id 2}])
           root (spin (el/ul (ifor-each :id (track xs) (fn [x] (el/li (str (:id x)))))))
           u (v2/observe! root (fn [_ _]))]
       (is (= ::none (error-of env root)))
       (fx/write! env xs [{:id 1} {:id 1}])
       (is (= ::addr/duplicate-key (error-of env root)))
       (fx/write! env xs [{:id 1} {}])
       (is (= ::addr/invalid-key (error-of env root)) "nil")
       (fx/write! env xs [{:id false}])
       (is (= ::addr/invalid-key (error-of env root)) "false")
       (u)))))

(defn- card
  "A component computation: the item is a computation of its own."
  [x]
  (el/component (el/li {:class "card"} (:v x))))

(deftest a-render-fn-returning-a-computation-is-awaited
  (fx/each-world
   (fn [env]
     (let [items (v2/signal [{:id 1 :v "a"} {:id 2 :v "b"}])
           root (spin (el/ul (ifor-each :id (track items) card)))
           {:keys [state] :as ctl} (fx/render! env root)]
       (is (= [[:ul {} [:li {:class "card"} "a"] [:li {:class "card"} "b"]]] (dom env)))
       (fx/write! env items [{:id 2 :v "b"} {:id 1 :v "A"}])
       (is (= [[:ul {} [:li {:class "card"} "b"] [:li {:class "card"} "A"]]] (dom env)))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

(deftest a-literal-render-fn-may-await
  (fx/each-world
   (fn [env]
     (let [items (v2/signal [{:id 1 :v "a"} {:id 2 :v "b"}])
           d (v2/deferred)
           root (spin (el/ul (ifor-each :id (track items)
                                        (fn [{:keys [v]}]
                                          (let [suffix (await d)]
                                            (el/li (str v suffix)))))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (is (= 0 (render/revision state)) "the items wait for the deferred")
       (v2/deliver! d "!")
       (fx/settle! env)
       (is (= [[:ul {} [:li {} "a!"] [:li {} "b!"]]] (dom env)))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

(deftest an-item-that-reruns-on-its-own-is-readopted-by-key
  ;; an item that tracks a source reruns on its own; the list's await-all
  ;; stores no continuation, so the list restarts from its body (T11) and
  ;; readopts the items, created before the fired edge, from its basis by
  ;; key. The counter before the track tells a resume from a new row.
  (fx/each-world
   (fn [env]
     (let [items (v2/signal [{:id 1 :v "a"} {:id 2 :v "b"}])
           sel (v2/signal 1)
           runs (atom {})
           root (spin (el/ul (ifor-each :id (track items)
                                        (fn [{:keys [id v]}]
                                          (swap! runs update id (fnil inc 0))
                                          (let [s (iv/get-new (track sel))]
                                            (el/li {:class (if (= s id) "sel" "")} v))))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (is (= [[:ul {} [:li {:class "sel"} "a"] [:li {:class ""} "b"]]] (dom env)))
       (let [before @runs]
         (fx/write! env sel 2)
         (is (= [[:ul {} [:li {:class ""} "a"] [:li {:class "sel"} "b"]]] (dom env)))
         (is (= {} (delta @runs before)) "each item resumes at its track, after the counter"))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

;; ---------------------------------------------------------------------------
;; Instances: one ifor-each site expanded twice in one run (through a
;; macro) keys its items under each instance's fragment address, so the
;; instances never adopt each other's items

#?(:clj
   (defmacro tagged-list
     "A list of `xs` whose item bodies count their runs under [tag id]. Every
      expansion has the same ifor-each source site."
     [xs runs tag]
     `(el/ul (ifor-each :id ~xs (fn [x#]
                                  (swap! ~runs update [~tag (:id x#)] (fnil inc 0))
                                  (el/li (str ~tag (:id x#))))))))

(deftest instances-of-one-site-keep-their-items
  (fx/each-world
   (fn [env]
     (let [a1 {:id 1} a2 {:id 2}
           as (v2/signal [a1 a2])
           bs (v2/signal [{:id 1} {:id 2}])
           runs (atom {})
           root (spin (let [xa (track as) xb (track bs)]
                        (el/div (tagged-list xa runs :a) (tagged-list xb runs :b))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (is (= {[:a 1] 1 [:a 2] 1 [:b 1] 1 [:b 2] 1} @runs))
       (let [before @runs]
         (fx/write! env as [a2])
         (is (= [[:div {} [:ul {} [:li {} ":a2"]] [:ul {} [:li {} ":b1"] [:li {} ":b2"]]]] (dom env)))
         (is (= {} (delta @runs before)) "list b's item 1 does not take list a's place"))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))
