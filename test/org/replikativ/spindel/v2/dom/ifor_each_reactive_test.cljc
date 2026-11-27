(ns org.replikativ.spindel.v2.dom.ifor-each-reactive-test
  "Port of the old `dom/ifor_each_reactive_test`: an `ifor-each` whose
   render fn returns a reactive computation (it tracks a source). When the
   source changes, every item's computation reruns and the list updates in
   place: no item is created again and no element of the list is inserted
   twice.

   The old bug was a stale per-call-site cache in `for-each*`'s spin path,
   which re-emitted :add deltas and duplicated DOM children. v2 has no such
   cache (phase-d design §4.3): the item's inner computation reruns, the
   item resumes at its await, and the list's `await-all` (a group await,
   which stores no continuation) restarts the list from its body, which
   readopts every item by its key (spec T11). The port checks the old
   intent on the committed DOM and the operation log, and adds the run
   counts that tell readoption from recreation, and a reverse followed by
   a tick: the reactive items move with their keys (no item body reruns,
   which fails without the keyed memo) and still update in place.

   API difference: the old render fn returned a raw `spin`; on v2 a plain
   function makes its computation with `el/component`, so its elements are
   placed at the item's DOM context (design §2.4)."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.foreach :refer [ifor-each]]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(defn- delta
  "The counts since `before`, keys with no increase left out."
  [counts before]
  (into {} (keep (fn [[k n]] (let [d (- n (get before k 0))] (when (pos? d) [k d])))) counts))

(deftest a-reactive-item-computation-updates-in-place
  (fx/each-world
   (fn [env]
     (let [d (:discharge (:mock env))
           log (:log (:mock env))
           tick (v2/signal 0)
           calls (atom {})                ; render fn calls: an item body run from its start
           runs (atom {})                 ; inner computation runs past its track
           render-fn (fn [x]
                       (swap! calls update (:id x) (fnil inc 0))
                       (el/component
                        (let [n (iv/get-new (track tick))]
                          (swap! runs update (:id x) (fnil inc 0))
                          (el/li (str (:id x) "-" n)))))
           [a b c :as xs] [{:id "a"} {:id "b"} {:id "c"}]
           items (v2/signal xs)
           root (spin (el/ul {:class "items"} (ifor-each :id (track items) render-fn)))
           {:keys [state] :as ctl} (fx/render! env root)
           uls (filterv #(and (= :create-element (:op %)) (= :ul (:tag %))) @log)
           ul (:id (first uls))
           lis (mock/children d ul)]
       (is (= [[:ul {:class "items"} [:li {} "a-0"] [:li {} "b-0"] [:li {} "c-0"]]] (mock/dom d :container)))
       (is (= 1 (count uls)) "exactly one ul is created")
       (is (= 3 (count lis)) "initial mount: the ul has 3 children")
       (is (= {"a" 1 "b" 1 "c" 1} @calls @runs))
       (doseq [n [1 2 3]]
         (testing (str "tick " n)
           (let [calls-before @calls
                 runs-before @runs]
             (reset! log [])
             (fx/write! env tick n)
             (is (= [[:ul {:class "items"} [:li {} (str "a-" n)] [:li {} (str "b-" n)] [:li {} (str "c-" n)]]]
                    (mock/dom d :container))
                 "each item shows the new tick")
             (is (= lis (mock/children d ul)) "the same three li elements, nothing inserted twice")
             (is (empty? (filter #(= :create-element (:op %)) @log)) "no element is created")
             (is (empty? (filter #(= ul (:parent %)) @log)) "no child operation on the ul")
             (is (= {"a" 1 "b" 1 "c" 1} (delta @runs runs-before)) "every inner computation reruns once")
             (is (= {} (delta @calls calls-before)) "no item body reruns: the list readopts its items by key"))))
       (testing "reverse, then tick: the reactive items move with their keys and still update in place"
         (let [calls-before @calls
               runs-before @runs
               [la lb lc] lis]
           (reset! log [])
           (fx/write! env items [c b a])     ; the same item objects: their captures are unchanged
           (is (= [[:ul {:class "items"} [:li {} "c-3"] [:li {} "b-3"] [:li {} "a-3"]]] (mock/dom d :container)))
           (is (= [lc lb la] (mock/children d ul)) "the li elements move")
           (fx/write! env tick 4)
           (is (= [[:ul {:class "items"} [:li {} "c-4"] [:li {} "b-4"] [:li {} "a-4"]]] (mock/dom d :container)))
           (is (= [lc lb la] (mock/children d ul)))
           (is (empty? (filter #(= :create-element (:op %)) @log)) "no element is created")
           (is (= {"a" 1 "b" 1 "c" 1} (delta @runs runs-before)) "the tick reruns every inner computation once")
           (is (= {} (delta @calls calls-before)) "neither the reverse nor the tick reruns an item body")))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))
