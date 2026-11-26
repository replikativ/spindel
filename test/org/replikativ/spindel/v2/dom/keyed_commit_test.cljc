(ns org.replikativ.spindel.v2.dom.keyed-commit-test
  "Keyed fragments in the v2 commit walk (sol's P4 review, findings 1-3).
   A keyed slot's items sit at the physical position of the slot: after the
   siblings before it, also when the fragment was empty, and also while
   other slots of the same element change in the same commit. An item
   whose key survives but whose element is replaced is a new subtree: it is
   seeded, not reconciled again, and its effects set up once. Keyed items
   are equal only with the same DOM identity (address)."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(defn- keyed
  "A KeyedFragment at `fa` with items keyed by `ks`."
  [fa ks items]
  (assoc (frag/keyed-fragment (vec items) nil) :addr fa :keys (vec ks)))

(defn- li [k] (el/li {:key k} (str k)))

(defn- dom [env] (mock/dom (:discharge (:mock env)) :container))

(deftest an-empty-fragment-grows-at-its-slot
  (fx/each-world
   (fn [env]
     (let [ks (v2/signal [])
           root (spin (let [xs (iv/get-new (track ks))]
                        (el/div (el/h1 "head") (keyed :frag-a xs (mapv li xs)) (el/footer "foot"))))
           ctl (fx/render! env root)]
       (fx/write! env ks ["a"])
       (is (= [[:div {} [:h1 {} "head"] [:li {} "a"] [:footer {} "foot"]]] (dom env))
           "the item goes after the heading, not before it")
       (fx/write! env ks ["a" "b"])
       (is (= [[:div {} [:h1 {} "head"] [:li {} "a"] [:li {} "b"] [:footer {} "foot"]]] (dom env)))
       (fx/unmount! env ctl)))))

(deftest a-fragment-grows-while-a-later-sibling-goes
  (fx/each-world
   (fn [env]
     (let [step (v2/signal 0)
           log (atom [])
           root (spin (let [s (iv/get-new (track step))
                            xs (if (zero? s) ["A"] ["A" "B"])]
                        (el/div (keyed :frag-b xs (mapv li xs))
                                (when (zero? s)
                                  (el/p {:ref (fn [el] (swap! log conj [:tail (some? el)]))} "tail")))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (fx/write! env step 1)
       (is (= [[:div {} [:li {} "A"] [:li {} "B"]]] (dom env)) "the tail is gone from the DOM")
       (is (= [[:tail true] [:tail false]] @log))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

(deftest a-replaced-item-under-a-surviving-key-is-a-new-subtree
  (fx/each-world
   (fn [env]
     (let [big (v2/signal false)
           log (atom [])
           r (fn [el] (swap! log conj [:p (some? el)]))
           root (spin (let [b (iv/get-new (track big))]
                        (el/section
                         (keyed :frag-c ["k"]
                                [(if b
                                   (el/div {:key "k"} (el/p {:ref r} "p"))
                                   (el/span {:key "k"} "s"))]))))
           {:keys [state] :as ctl} (fx/render! env root)]
       (fx/write! env big true)
       (is (= [[:section {} [:div {} [:p {} "p"]]]] (dom env)) "the new subtree's children are created once")
       (is (= [[:p true]] @log) "its ref is set up once")
       (is (= 1 (count (filter #(contains? % :ref) (vals (render/ledger state))))) "one ledger entry")
       (fx/unmount! env ctl)
       (is (= [[:p true] [:p false]] @log) "and claimed once")
       (is (empty? (fx/leftovers env state)))))))

(deftest equal-looking-items-at-other-addresses-are-different
  (fx/each-world
   (fn [env]
     (let [branch (v2/signal true)
           log (atom [])
           root (spin (let [b (iv/get-new (track branch))]
                        (el/section
                         (keyed :frag-d ["k"]
                                [(if b
                                   (el/span {:key "k" :ref (fn [el] (swap! log conj [:one (some? el)]))} "x")
                                   (el/span {:key "k" :ref (fn [el] (swap! log conj [:two (some? el)]))} "x"))]))))
           {:keys [state] :as ctl} (fx/render! env root)
           a1 (:addr (first (:children (render/committed state))))]
       (fx/write! env branch false)
       (let [a2 (:addr (first (:children (render/committed state))))]
         (is (not= a1 a2) "two addresses")
         (is (some? (get @(:elements (:mock env)) a2)) "the new address has its element")
         (is (nil? (get @(:elements (:mock env)) a1))))
       (is (= [[:one true] [:one false] [:two true]] @log) "the old element is cleaned up, the new one mounted")
       (is (= [[:section {} [:span {} "x"]]] (dom env)))
       (is (empty? (fx/violations)) "no unbound address")
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

;; ---------------------------------------------------------------------------
;; Whole fragments moving across slots (sol's confirmation pass, P1): a
;; slot whose fragment is another one than the slot's previous fragment is
;; replaced, so its items are recreated: cleaned up and set up once each

(defn- fragments-root
  "A div holding, slot by slot, the fragments named in `order` (a signal of
   fragment names); fragment n holds one item keyed n, with a ref logging
   [n attached?]."
  [order log]
  (spin (let [ns (iv/get-new (track order))]
          (el/div (mapv (fn [n]
                          (keyed (keyword (str "frag-" n)) [n]
                                 [(el/li {:key n :ref (fn [el] (swap! log conj [n (some? el)]))} n)]))
                        ns)))))

(deftest fragments-swap-slots
  (fx/each-world
   (fn [env]
     (let [order (v2/signal ["F" "G"])
           log (atom [])
           {:keys [state] :as ctl} (fx/render! env (fragments-root order log))]
       (fx/write! env order ["G" "F"])
       (is (= [[:div {} [:li {} "G"] [:li {} "F"]]] (dom env)) "the DOM follows the slots")
       (is (= #{["F" true] ["G" true] ["F" false] ["G" false]} (set (take 4 @log))))
       (is (= [["F" true] ["G" true]] (take 2 @log)))
       (is (= 1 (count (filter #{["F" false]} @log))) "F's item is cleaned up once")
       (is (= 2 (count (filter #{["F" true]} @log))) "and set up once more")
       (is (= 2 (count (render/ledger state))) "one ledger entry per item")
       (fx/unmount! env ctl)
       (is (= (frequencies (map first @log)) {"F" 4 "G" 4}) "every setup claimed once")
       (is (empty? (fx/leftovers env state)))))))

(deftest three-fragments-rotate
  (fx/each-world
   (fn [env]
     (let [order (v2/signal ["F" "G" "H"])
           log (atom [])
           {:keys [state] :as ctl} (fx/render! env (fragments-root order log))]
       (fx/write! env order ["G" "H" "F"])
       (is (= [[:div {} [:li {} "G"] [:li {} "H"] [:li {} "F"]]] (dom env)))
       (fx/write! env order ["F" "G" "H"])
       (is (= [[:div {} [:li {} "F"] [:li {} "G"] [:li {} "H"]]] (dom env)))
       (is (= 3 (count (render/ledger state))))
       (fx/unmount! env ctl)
       (is (= (frequencies (map first @log)) {"F" 6 "G" 6 "H" 6}) "every setup claimed once")
       (is (empty? (fx/leftovers env state)))))))
