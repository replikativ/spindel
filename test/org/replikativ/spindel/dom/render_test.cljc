(ns org.replikativ.spindel.dom.render-test
  "Tests for delta-direct reactive rendering.

  These tests verify that:
  1. Initial render creates DOM elements
  2. Signal changes produce deltas (not full re-renders)
  3. Deltas flow through to discharge operations
  4. Only changed parts of DOM are updated"
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.dom.core :as dom]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
            #?(:clj [org.replikativ.spindel.test-async :refer [await-drain]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.dom.foreach :refer [ifor-each]])))

;; =============================================================================
;; Element Macro Tests (without execution context - simple mode)
;; =============================================================================

(deftest test-element-macros-simple
  (testing "Element macros work without execution context (simple mode)"
    (let [v (el/div {:class "test"} (el/span "Hello"))]
      (is (= :div (:tag v)))
      (is (= {:class "test"} @(:attrs v)))
      (is (= 1 (count @(:children v))))
      (is (= :span (:tag (first @(:children v))))))))

(deftest test-element-macros-nested
  (testing "Nested elements work without execution context"
    (let [v (el/ul {:class "list"}
              (el/li {:key "1"} "Item 1")
              (el/li {:key "2"} "Item 2"))]
      (is (= :ul (:tag v)))
      (is (= 2 (count @(:children v))))
      (is (= "1" (:key (first @(:children v))))))))

(deftest test-element-macros-text-coercion
  (testing "Text and numbers are coerced to text nodes"
    (let [v (el/p "Hello " 42 " times")]
      (is (= 3 (count @(:children v))))
      (is (every? dom/text-node? @(:children v))))))

;; =============================================================================
;; Initial Mount Tests
;; =============================================================================

(deftest test-initial-mount
  (testing "Initial mount creates elements"
    (let [{:keys [discharge log]} (disch/make-mock-discharge)
          vdom (el/div {:class "app"}
                 (el/h1 "Hello")
                 (el/p "World"))
          container nil
          state (render/->RenderState container discharge nil false)
          mounted-state (render/initial-mount! state vdom)]
      (is (:mounted? mounted-state))
      (is (some? (:current-vdom mounted-state)))
      (let [ops @log]
        (is (= 3 (count (filter #(= :create-element (:op %)) ops))))))))

(deftest test-update-render-no-deltas
  (testing "Update render with no deltas does minimal work"
    ;; Ensure no execution context is bound (could leak from previous tests)
    (binding [rtc/*execution-context* nil]
      (let [{:keys [discharge log]} (disch/make-mock-discharge)
            v1 (el/div {:class "same"})
            container nil
            state (render/->RenderState container discharge nil false)
            mounted (render/initial-mount! state v1)
            _ (reset! log [])
            v2 (el/div {:class "same"})
            _updated (render/update-render-with-transfer! mounted v2)]
        ;; Without execution context, no deltas, so no DOM operations
        (is (empty? @log))))))

;; =============================================================================
;; KeyedFragment Tests
;; =============================================================================

(deftest test-keyed-fragment-creation
  (testing "KeyedFragment can be created directly"
    (let [items [(el/li "A") (el/li "B") (el/li "C")]
          frag (frag/keyed-fragment items nil)]
      (is (frag/keyed-fragment? frag))
      (is (= 3 (count (frag/fragment-items frag))))
      (is (nil? (frag/fragment-deltas frag))))))

(deftest test-keyed-fragment-with-deltas
  (testing "KeyedFragment can carry deltas"
    (let [items [(el/li "A") (el/li "B")]
          deltas [{:delta :add :path [1] :value (el/li "B")}]
          frag (frag/keyed-fragment items deltas)]
      (is (= deltas (frag/fragment-deltas frag))))))

(deftest test-keyed-fragment-deref
  (testing "KeyedFragment can be derefed to get items"
    (let [items [(el/li "X") (el/li "Y")]
          frag (frag/keyed-fragment items nil)]
      (is (= items @frag)))))

(deftest test-discharge-keyed-fragment
  (testing "Discharge renders KeyedFragment items"
    (let [{:keys [discharge log]} (disch/make-mock-discharge)
          items [(el/li "A") (el/li "B")]
          frag (frag/keyed-fragment items nil)]
      (disch/render-initial! discharge frag)
      (let [ops @log]
        (is (= 2 (count (filter #(and (= :create-element (:op %))
                                      (= :li (:tag %))) ops))))
        (is (= 2 (count (filter #(= :create-text (:op %)) ops))))))))

;; =============================================================================
;; Element Reference Transfer Tests
;; =============================================================================

(deftest test-transfer-element-refs
  (testing "Element references are transferred between vdom trees"
    (let [{:keys [discharge]} (disch/make-mock-discharge)
          v1 (el/div {:class "test"} (el/span "Hello"))
          _ (disch/render-initial! discharge v1)
          v2 (el/div {:class "test"} (el/span "Hello"))]
      (render/transfer-element-refs! discharge v1 v2)
      (is (some? (disch/get-element discharge v2))))))

;; =============================================================================
;; Delta-Direct Rendering Tests (CLJ only - requires await-drain)
;; =============================================================================

#?(:clj
   (deftest test-initial-render-creates-elements
     (testing "Initial render creates all DOM elements"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge log]} (disch/make-mock-discharge)
                 counter (sig/signal 0)
                 render-spin (spin
                               (let [iv (track counter)
                                     current-val @iv]
                                 (el/div {:class "counter"}
                                   (el/span (str "Count: " current-val)))))
                 container nil]
             (render/render-spin! container render-spin discharge)
             @render-spin

             ;; Verify elements were created
             (is (= 2 (count (filter #(= :create-element (:op %)) @log)))
                 "Should create div and span")
             (is (= 1 (count (filter #(= :create-text (:op %)) @log)))
                 "Should create text node")
             (is (some #(and (= :create-text (:op %))
                             (= "Count: 0" (:text %))) @log)
                 "Text should be 'Count: 0'")))))))

#?(:clj
   (deftest test-signal-update-triggers-rerender
     (testing "Signal update triggers spin re-execution"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge]} (disch/make-mock-discharge)
                 counter (sig/signal 0)
                 render-count (atom 0)
                 last-value (atom nil)
                 render-spin (spin
                               (let [iv (track counter)
                                     current-val @iv]
                                 (swap! render-count inc)
                                 (reset! last-value current-val)
                                 (el/div {:class "counter"}
                                   (el/span (str "Count: " current-val)))))
                 container nil]
             (render/render-spin! container render-spin discharge)
             @render-spin

             (is (= 1 @render-count))
             (is (= 0 @last-value))

             ;; Update signal
             (swap! counter inc)
             (await-drain rt)

             (is (= 2 @render-count) "Should re-render after signal change")
             (is (= 1 @last-value) "Should render with new value")))))))

#?(:clj
   (deftest test-deltaable-collection-deltas-available
     (testing "Deltaable collection deltas are available in track"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge]} (disch/make-mock-discharge)
                 items (sig/signal [])
                 captured-deltas (atom nil)
                 render-spin (spin
                               (let [iv (track items)
                                     current @iv
                                     deltas (iv/get-deltas iv)]
                                 ;; Capture deltas for verification
                                 (reset! captured-deltas deltas)
                                 (el/ul {:class "items"}
                                   (foreach/ifor-each :id current
                                     (fn [item] (el/li (:text item)))))))
                 container nil]
             (render/render-spin! container render-spin discharge)
             @render-spin

             ;; Initial render - no deltas (empty vector)
             (is (empty? @captured-deltas) "Initial empty vector has no deltas")

             ;; Add item - should produce :add delta
             (swap! items conj {:id "1" :text "Item 1"})
             (await-drain rt)

             ;; Verify delta was captured
             (is (seq @captured-deltas) "Should have deltas after conj")
             (is (= :add (:delta (first @captured-deltas)))
                 "Delta should be :add")
             (is (= [0] (:path (first @captured-deltas)))
                 "Delta path should be [0]")))))))

#?(:clj
   (deftest test-multiple-updates-produce-deltas
     (testing "Multiple signal updates produce corresponding deltas"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge]} (disch/make-mock-discharge)
                 items (sig/signal [])
                 delta-history (atom [])
                 render-spin (spin
                               (let [iv (track items)
                                     current @iv
                                     deltas (iv/get-deltas iv)]
                                 ;; Accumulate deltas
                                 (when (seq deltas)
                                   (swap! delta-history conj deltas))
                                 (el/ul {:class "items"}
                                   (foreach/ifor-each :id current
                                     (fn [item] (el/li (:text item)))))))
                 container nil]
             (render/render-spin! container render-spin discharge)
             @render-spin

             ;; Add first item
             (swap! items conj {:id "1" :text "First"})
             (await-drain rt)

             ;; Add second item
             (swap! items conj {:id "2" :text "Second"})
             (await-drain rt)

             ;; Update first item
             (swap! items assoc 0 {:id "1" :text "Updated First"})
             (await-drain rt)

             ;; Verify delta history
             (is (= 3 (count @delta-history))
                 "Should have 3 sets of deltas")

             ;; First add
             (is (= :add (:delta (first (nth @delta-history 0)))))
             (is (= [0] (:path (first (nth @delta-history 0)))))

             ;; Second add
             (is (= :add (:delta (first (nth @delta-history 1)))))
             (is (= [1] (:path (first (nth @delta-history 1)))))

             ;; Update
             (is (= :update (:delta (first (nth @delta-history 2)))))
             (is (= [0] (:path (first (nth @delta-history 2)))))))))))

#?(:clj
   (deftest test-remove-produces-remove-delta
     (testing "Removing from deltaable produces :remove delta"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge]} (disch/make-mock-discharge)
                 items (sig/signal [{:id "1" :text "A"}
                                    {:id "2" :text "B"}
                                    {:id "3" :text "C"}])
                 captured-deltas (atom nil)
                 render-spin (spin
                               (let [iv (track items)
                                     current @iv
                                     deltas (iv/get-deltas iv)]
                                 (reset! captured-deltas deltas)
                                 (el/ul {:class "items"}
                                   (foreach/ifor-each :id current
                                     (fn [item] (el/li (:text item)))))))
                 container nil]
             (render/render-spin! container render-spin discharge)
             @render-spin

             ;; Remove middle item using remove-at
             (swap! items (fn [v] (d/remove-at v 1)))
             (await-drain rt)

             ;; Verify :remove delta
             (is (seq @captured-deltas) "Should have deltas")
             (is (= :remove (:delta (first @captured-deltas)))
                 "Delta should be :remove")
             (is (= [1] (:path (first @captured-deltas)))
                 "Should remove at index 1")
             (is (= {:id "2" :text "B"} (:old-value (first @captured-deltas)))
                 "Should capture old value")))))))

#?(:clj
   (deftest test-filter-vec-produces-multiple-remove-deltas
     (testing "filter-vec produces :remove delta for each filtered item"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge]} (disch/make-mock-discharge)
                 items (sig/signal [{:id "1" :done false}
                                    {:id "2" :done true}
                                    {:id "3" :done false}
                                    {:id "4" :done true}])
                 captured-deltas (atom nil)
                 render-spin (spin
                               (let [iv (track items)
                                     current @iv
                                     deltas (iv/get-deltas iv)]
                                 (reset! captured-deltas deltas)
                                 (el/ul {:class "items"}
                                   (foreach/ifor-each :id current
                                     (fn [item] (el/li (:id item)))))))
                 container nil]
             (render/render-spin! container render-spin discharge)
             @render-spin

             ;; Filter out done items
             (swap! items (fn [v] (d/filter-vec #(not (:done %)) v)))
             (await-drain rt)

             ;; Should have 2 :remove deltas (for items 2 and 4)
             (is (= 2 (count @captured-deltas))
                 "Should have 2 remove deltas")
             (is (every? #(= :remove (:delta %)) @captured-deltas)
                 "All deltas should be :remove")))))))

#?(:clj
   (deftest test-render-count-matches-signal-updates
     (testing "Render count matches number of signal updates"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge]} (disch/make-mock-discharge)
                 counter (sig/signal 0)
                 render-count (atom 0)
                 render-spin (spin
                               (let [iv (track counter)
                                     current-val @iv]
                                 (swap! render-count inc)
                                 (el/div {:class "counter"}
                                   (el/span (str "Count: " current-val)))))
                 container nil]
             (render/render-spin! container render-spin discharge)
             @render-spin

             (is (= 1 @render-count) "Initial render")

             ;; 5 updates
             (dotimes [_ 5]
               (swap! counter inc)
               (await-drain rt))

             (is (= 6 @render-count) "1 initial + 5 updates")))))))

#?(:clj
   (deftest test-old-value-available-in-interval
     (testing "Old value is available via interval for comparison"
       (let [rt (ctx/create-execution-context)]
         (binding [rtc/*execution-context* rt]
           (let [{:keys [discharge]} (disch/make-mock-discharge)
                 counter (sig/signal 0)
                 captured-old (atom nil)
                 captured-new (atom nil)
                 render-spin (spin
                               (let [iv (track counter)
                                     new-val @iv
                                     old-val (nth iv 1)]
                                 (reset! captured-new new-val)
                                 (reset! captured-old old-val)
                                 (el/div {:class "counter"}
                                   (el/span (str "Count: " new-val)))))
                 container nil]
             (render/render-spin! container render-spin discharge)
             @render-spin

             ;; Initial: new=0, old=nil (no previous)
             (is (= 0 @captured-new))
             ;; Note: old value on first render depends on signal impl

             ;; Update
             (swap! counter inc)
             (await-drain rt)

             (is (= 1 @captured-new) "New value should be 1")
             (is (= 0 @captured-old) "Old value should be 0")))))))
