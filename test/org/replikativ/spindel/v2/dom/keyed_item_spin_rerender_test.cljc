(ns org.replikativ.spindel.v2.dom.keyed-item-spin-rerender-test
  "Port of the old `dom/keyed_item_spin_rerender_test`: an `ifor-each`
   item whose render fn returns a computation keeps its keyed element
   address when the list's parent reruns, whether the parent tracks a
   source itself or a source tracked deep inside the item escalates the
   rerun (the old property-box DOM-duplication bug: the column re-addressed
   structurally, failed to reconcile and was recreated).

   On v2 an item's DOM context is its keyed address under the fragment's
   address (phase-d design §4.3), fixed by the list, not by a dynamic
   extent of the first run. The port compares the committed vdom's
   addresses before and after the rerun, as the old test did, and adds
   the committed DOM facts (no element created, the same children) and run
   counts: the parent's rerun readopts the columns by key without running
   them; a deep track reruns only the inner computations, the columns
   resume at their awaits, and the list restarts from its body (its
   `await-all` stores no continuation, spec T11). The first case also
   swaps the columns: each keeps its address and element and none runs
   (the keyed memo, design §4.3).

   API differences: a plain function makes its computation with
   `el/component` (design §2.4), and the column root needs no `:key`: the
   item's context is already keyed."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track await]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.foreach :refer [ifor-each]]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(defn- class-addrs
  "{class -> :addr} of every element of vnode tree `node` with a class."
  [node]
  (if (and (map? node) (keyword? (:tag node)))
    (apply merge
           (if-let [c (:class (:attrs node))] {c (:addr node)} {})
           (map class-addrs (:children node)))
    {}))

(defn- delta
  "The counts since `before`, keys with no increase left out."
  [counts before]
  (into {} (keep (fn [[k n]] (let [d (- n (get before k 0))] (when (pos? d) [k d])))) counts))

(def ^:private columns [{:id "col-1" :title "Column 1"} {:id "col-2" :title "Column 2"}])

(defn- container-children
  "The element ids under the committed container div."
  [d]
  (mock/children d (first (mock/children d :container))))

(deftest an-item-keeps-its-address-when-its-parent-reruns
  (fx/each-world
   (fn [env]
     (let [d (:discharge (:mock env))
           log (:log (:mock env))
           trigger (v2/signal 0)
           column-runs (atom {})
           render-column (fn [col]
                           (el/component
                            (swap! column-runs update (:id col) (fnil inc 0))
                            (el/div {:class (str "column-" (:id col))} (el/span (:title col)))))
           cols (v2/signal columns)
           root-runs (atom 0)
           root (spin (let [t (iv/get-new (track trigger))
                            cs (track cols)]
                        (swap! root-runs inc)
                        (el/div {:class "columns-container"}
                                (el/span {:class "t"} (str t))
                                (ifor-each :id cs render-column))))
           {:keys [state] :as ctl} (fx/render! env root)
           r1 (class-addrs (render/committed state))
           kids (container-children d)
           rev (render/revision state)
           column-before @column-runs
           root-before @root-runs]
       (is (= {"col-1" 1 "col-2" 1} column-before))
       (reset! log [])
       (fx/write! env trigger 1)
       (let [r2 (class-addrs (render/committed state))]
         (is (< rev (render/revision state)) "the parent's rerun is committed")
         (is (= 1 (- @root-runs root-before)) "the parent reruns once")
         (is (= {} (delta @column-runs column-before)) "the columns are readopted by key, not run")
         (doseq [cls ["columns-container" "t" "column-col-1" "column-col-2"]]
           (is (some? (get r1 cls)) cls)
           (is (= (get r1 cls) (get r2 cls)) (str cls ": the address is stable across the parent's rerun"))))
       (is (= [[:div {:class "columns-container"}
                [:span {:class "t"} "1"]
                [:div {:class "column-col-1"} [:span {} "Column 1"]]
                [:div {:class "column-col-2"} [:span {} "Column 2"]]]]
              (mock/dom d :container)))
       (is (= kids (container-children d)) "the same children: nothing recreated")
       (is (empty? (filter #(= :create-element (:op %)) @log)) "no element is created")
       (testing "the columns swap places: each keeps its address and element, none runs"
         (let [r1 (class-addrs (render/committed state))
               [t c1 c2] (container-children d)
               column-before @column-runs]
           (reset! log [])
           (fx/write! env cols (vec (reverse columns)))
           (is (= r1 (class-addrs (render/committed state))))
           (is (= [t c2 c1] (container-children d)))
           (is (= {} (delta @column-runs column-before)) "the columns are readopted by key, not run")
           (is (empty? (filter #(= :create-element (:op %)) @log)) "no element is created")))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))

(deftest an-item-keeps-its-address-when-a-deep-track-escalates
  (fx/each-world
   (fn [env]
     (let [d (:discharge (:mock env))
           log (:log (:mock env))
           trigger (v2/signal 0)
           inner-runs (atom {})
           column-runs (atom {})
           ;; the property-box analog: a computation inside the column
           ;; tracks `trigger`
           render-inner (fn [col]
                          (el/component
                           (let [v (iv/get-new (track trigger))]
                             (swap! inner-runs update (:id col) (fnil inc 0))
                             (el/div {:class (str "inner-" (:id col))} (str (:title col) "-" v)))))
           render-column (fn [col]
                           (el/component
                            (swap! column-runs update (:id col) (fnil inc 0))
                            (let [inner (await (render-inner col))]
                              (el/div {:class (str "column-" (:id col))} inner))))
           root-runs (atom 0)
           root (spin (swap! root-runs inc)
                      (el/div {:class "columns-container"} (ifor-each :id columns render-column)))
           {:keys [state] :as ctl} (fx/render! env root)
           r1 (class-addrs (render/committed state))
           kids (container-children d)
           inner-before @inner-runs
           column-before @column-runs
           root-before @root-runs]
       (is (= {"col-1" 1 "col-2" 1} inner-before column-before))
       (reset! log [])
       (fx/write! env trigger 1)
       (let [r2 (class-addrs (render/committed state))]
         (is (= {"col-1" 1 "col-2" 1} (delta @inner-runs inner-before)) "each inner computation reruns once")
         (is (= {} (delta @column-runs column-before)) "the columns resume at their awaits")
         (is (pos? (- @root-runs root-before)) "the list restarts from its body")
         (doseq [cls ["columns-container" "column-col-1" "column-col-2" "inner-col-1" "inner-col-2"]]
           (is (some? (get r1 cls)) cls)
           (is (= (get r1 cls) (get r2 cls)) (str cls ": the address is stable across the escalated rerun"))))
       (is (= [[:div {:class "columns-container"}
                [:div {:class "column-col-1"} [:div {:class "inner-col-1"} "Column 1-1"]]
                [:div {:class "column-col-2"} [:div {:class "inner-col-2"} "Column 2-1"]]]]
              (mock/dom d :container)))
       (is (= kids (container-children d)) "the same children: nothing recreated")
       (is (empty? (filter #(= :create-element (:op %)) @log)) "no element is created")
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))
