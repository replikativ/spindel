(ns is.simm.spindel.dom.ifor-each-spin-test
  "Tests for ifor-each-spin - spin-returning render functions.

  These tests mirror the simmis columns pattern:
  1. Parent spin awaits ifor-each-spin
  2. Each render-fn returns a spin that may do nested awaits
  3. The whole chain should complete properly"
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [is.simm.spindel.dom.elements :as el]
            [is.simm.spindel.dom.fragment :as frag]
            [is.simm.spindel.dom.foreach :as foreach]
            [is.simm.spindel.effects.await :refer [await]]
            [is.simm.spindel.spin.core :as spin-core]
            [is.simm.spindel.spin.combinators :as combinators]
            [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.runtime.context :as ctx]
            [is.simm.spindel.test-helpers :refer [async with-ctx run-spin!]]
            #?(:clj [is.simm.spindel.spin.cps :refer [spin]]))
  #?(:cljs (:require-macros [is.simm.spindel.spin.cps :refer [spin]]
                            [is.simm.spindel.test-helpers :refer [async with-ctx]]
                            [is.simm.spindel.dom.foreach :refer [ifor-each-spin]])))

;; =============================================================================
;; Basic ifor-each-spin Tests
;; =============================================================================

(deftest test-ifor-each-spin-basic
  (testing "ifor-each-spin with simple spin render functions"
    (async done
      (with-ctx [_ctx]
        (let [items [{:id "a" :text "Item A"}
                     {:id "b" :text "Item B"}
                     {:id "c" :text "Item C"}]
              ;; Simple render function that returns a spin
              render-fn (fn [item]
                          (spin
                            (el/li {:key (:id item)} (:text item))))
              ;; Parent spin awaits ifor-each-spin
              parent-spin (spin
                            (let [frag (await (foreach/for-each-spin*
                                                {:file "test" :line 1 :column 1}
                                                :id
                                                render-fn
                                                items))]
                              frag))]
          ;; Execute with run-spin! and callback
          (run-spin! parent-spin
                     (fn [result]
                       (is (frag/keyed-fragment? result) "Result should be a KeyedFragment")
                       (is (= 3 (count (frag/fragment-items result))) "Should have 3 items")
                       (done))
                     (fn [err]
                       (is false (str "Spin failed: " err))
                       (done))))))))

(deftest test-ifor-each-spin-nested-await
  (testing "ifor-each-spin with nested awaits in render function (simmis pattern)"
    (async done
      (with-ctx [_ctx]
        (let [columns [{:id "col-1" :title "Column 1"}
                       {:id "col-2" :title "Column 2"}]

              ;; Inner spin that simulates render-tab-content
              render-tab-content (fn [title]
                                   (spin
                                     (el/div {:class "content"} title)))

              ;; Column render function that awaits inner spin
              ;; This mirrors simmis render-column pattern
              render-column (fn [col]
                              (spin
                                (let [content (await (render-tab-content (:title col)))]
                                  (el/div {:key (:id col) :class "column"}
                                    content))))

              ;; Parent spin that awaits ifor-each-spin
              ;; This mirrors simmis render-columns-container pattern
              parent-spin (spin
                            (let [frag (await (foreach/for-each-spin*
                                                {:file "test" :line 1 :column 1}
                                                :id
                                                render-column
                                                columns))]
                              (el/div {:class "columns-container"}
                                frag)))]

          ;; Execute with run-spin!
          (run-spin! parent-spin
                     (fn [result]
                       (is (map? result) "Result should be a vnode")
                       (is (= :div (:tag result)) "Result should be a div")
                       (done))
                     (fn [err]
                       (is false (str "Spin failed: " err))
                       (done))))))))

(deftest test-ifor-each-spin-deeply-nested
  (testing "ifor-each-spin with deeply nested await chain"
    (async done
      (with-ctx [_ctx]
        (let [items [{:id "1"}]

              ;; Level 3: deepest spin
              level-3 (fn []
                        (spin
                          (el/span "deep")))

              ;; Level 2: awaits level 3
              level-2 (fn []
                        (spin
                          (let [inner (await (level-3))]
                            (el/div {:class "level-2"} inner))))

              ;; Level 1: render function that awaits level 2
              render-fn (fn [item]
                          (spin
                            (let [content (await (level-2))]
                              (el/div {:key (:id item) :class "level-1"}
                                content))))

              ;; Parent: awaits ifor-each-spin
              parent-spin (spin
                            (let [frag (await (foreach/for-each-spin*
                                                {:file "test" :line 1 :column 1}
                                                :id
                                                render-fn
                                                items))]
                              frag))]

          ;; Execute
          (run-spin! parent-spin
                     (fn [result]
                       (is (frag/keyed-fragment? result) "Should be a fragment")
                       (done))
                     (fn [err]
                       (is false (str "Spin failed: " err))
                       (done))))))))

(deftest test-parallel-with-bindings-child-completion
  (testing "parallel-with-bindings children should complete and call on-ok"
    (async done
      (with-ctx [_ctx]
        (let [;; Create child spins manually
              child-1 (spin-core/make-spin
                        (fn [resolve _reject]
                          (resolve "child-1-result"))
                        :child-1)
              child-2 (spin-core/make-spin
                        (fn [resolve _reject]
                          (resolve "child-2-result"))
                        :child-2)

              ;; Parent awaits parallel
              parent-spin (spin
                            (let [results (await (combinators/parallel-with-bindings
                                                   {:spin child-1 :bindings {}}
                                                   {:spin child-2 :bindings {}}))]
                              results))]

          ;; Execute
          (run-spin! parent-spin
                     (fn [result]
                       (is (= ["child-1-result" "child-2-result"] result) "Should get results")
                       (done))
                     (fn [err]
                       (is false (str "Spin failed: " err))
                       (done))))))))
