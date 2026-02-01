(ns org.replikativ.spindel.dom.ref-test
  "Tests for ref callback support in DOM discharge."
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.dom.core :as dom]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.foreign :as foreign]))

;; =============================================================================
;; Ref Callback Tests
;; =============================================================================

(deftest test-ref-callback-on-mount
  (testing "Ref callback is called with element on mount"
    (let [ref-calls (atom [])
          ref-fn (fn [el] (swap! ref-calls conj {:event :call :el el}))
          {:keys [discharge]} (disch/make-mock-discharge)
          app (dom/make-vnode :div {:ref ref-fn})]
      (disch/render-initial! discharge app)
      ;; Ref callback should have been called once with the element
      (is (= 1 (count @ref-calls)))
      (let [call (first @ref-calls)]
        (is (= :call (:event call)))
        ;; Element should be a mock element ID (gensym)
        (is (some? (:el call)))))))

(deftest test-ref-callback-on-nested-mount
  (testing "Ref callbacks are called for nested elements"
    (let [outer-calls (atom [])
          inner-calls (atom [])
          {:keys [discharge]} (disch/make-mock-discharge)
          app (dom/make-vnode :div {:ref (fn [el] (swap! outer-calls conj el))}
                              [(dom/make-vnode :span {:ref (fn [el] (swap! inner-calls conj el))})])]
      (disch/render-initial! discharge app)
      (is (= 1 (count @outer-calls)))
      (is (= 1 (count @inner-calls))))))

(deftest test-ref-callback-on-remove
  (testing "Ref callback is called with nil on remove"
    (let [ref-calls (atom [])
          ref-fn (fn [el] (swap! ref-calls conj el))
          vnode (dom/make-vnode :div {:ref ref-fn})
          {:keys [discharge]} (disch/make-mock-discharge)
          parent-el :mock-parent]
      ;; First render the element
      (let [el (disch/render-initial! discharge vnode)]
        ;; Clear the mount call
        (reset! ref-calls [])
        ;; Now apply a remove delta
        (disch/apply-child-delta! discharge parent-el
                                   {:delta :remove :path [0] :old-value vnode})
        ;; Ref should have been called with nil
        (is (= 1 (count @ref-calls)))
        (is (nil? (first @ref-calls)))))))

(deftest test-ref-callback-on-update
  (testing "Ref callbacks are called for old and new vnodes on update"
    (let [old-calls (atom [])
          new-calls (atom [])
          old-vnode (dom/make-vnode :div {:ref (fn [el] (swap! old-calls conj el))})
          new-vnode (dom/make-vnode :span {:ref (fn [el] (swap! new-calls conj el))})
          {:keys [discharge]} (disch/make-mock-discharge)
          parent-el :mock-parent]
      ;; First render the old element
      (disch/render-initial! discharge old-vnode)
      ;; Clear calls
      (reset! old-calls [])
      (reset! new-calls [])
      ;; Apply update delta
      (disch/apply-child-delta! discharge parent-el
                                 {:delta :update :path [0]
                                  :old-value old-vnode
                                  :value new-vnode})
      ;; Old ref should have been called with nil (unmount)
      (is (= 1 (count @old-calls)))
      (is (nil? (first @old-calls)))
      ;; New ref should have been called with element (mount)
      (is (= 1 (count @new-calls)))
      (is (some? (first @new-calls))))))

(deftest test-ref-error-handling
  (testing "Ref callback errors are caught and don't crash discharge"
    (let [error-thrown (atom false)
          ref-fn (fn [_el]
                   (reset! error-thrown true)
                   (throw (#?(:clj Exception. :cljs js/Error.) "Test error")))
          {:keys [discharge]} (disch/make-mock-discharge)
          app (dom/make-vnode :div {:ref ref-fn})]
      ;; Should not throw
      (disch/render-initial! discharge app)
      (is @error-thrown "Ref function should have been called"))))

;; =============================================================================
;; Foreign Node Tests
;; =============================================================================

(deftest test-foreign-node-creation
  (testing "foreign-node creates a vnode without context"
    (let [mount-calls (atom [])
          unmount-calls (atom [])
          vnode (foreign/foreign-node*
                  {:file "test" :line 1 :column 1}
                  {:class "editor"
                   :on-mount (fn [el] (swap! mount-calls conj el))
                   :on-unmount (fn [_] (swap! unmount-calls conj :unmount))})]
      (is (= :div (:tag vnode)))
      (is (= {:class "editor"} @(:attrs vnode)))
      (is (fn? (:ref vnode))))))

(deftest test-foreign-node-with-custom-tag
  (testing "foreign-node respects custom tag"
    (let [vnode (foreign/foreign-node*
                  {:file "test" :line 1 :column 1}
                  {:tag :pre
                   :class "code"})]
      (is (= :pre (:tag vnode))))))

(deftest test-foreign-node-mount-callback
  (testing "foreign-node mount callback is called during render"
    (let [mount-calls (atom [])
          vnode (foreign/foreign-node*
                  {:file "test" :line 1 :column 1}
                  {:on-mount (fn [el] (swap! mount-calls conj el))})
          {:keys [discharge]} (disch/make-mock-discharge)]
      ;; Render the foreign node
      (disch/render-initial! discharge vnode)
      ;; Mount callback should have been called via ref
      (is (= 1 (count @mount-calls)))
      (is (some? (first @mount-calls))))))

(deftest test-foreign-node-unmount-callback
  (testing "foreign-node unmount callback is called on remove"
    (let [unmount-calls (atom [])
          vnode (foreign/foreign-node*
                  {:file "test" :line 1 :column 1}
                  {:on-unmount (fn [_] (swap! unmount-calls conj :unmounted))})
          {:keys [discharge]} (disch/make-mock-discharge)
          parent-el :mock-parent]
      ;; First render
      (disch/render-initial! discharge vnode)
      (is (empty? @unmount-calls) "Unmount should not be called yet")
      ;; Apply remove delta
      (disch/apply-child-delta! discharge parent-el
                                 {:delta :remove :path [0] :old-value vnode})
      (is (= 1 (count @unmount-calls))))))

(deftest test-foreign-node-error-handling
  (testing "foreign-node callback errors are caught"
    (let [mount-error (atom false)
          unmount-error (atom false)
          vnode (foreign/foreign-node*
                  {:file "test" :line 1 :column 1}
                  {:on-mount (fn [_]
                               (reset! mount-error true)
                               (throw (#?(:clj Exception. :cljs js/Error.) "Mount error")))
                   :on-unmount (fn [_]
                                 (reset! unmount-error true)
                                 (throw (#?(:clj Exception. :cljs js/Error.) "Unmount error")))})
          {:keys [discharge]} (disch/make-mock-discharge)
          parent-el :mock-parent]
      ;; Should not throw on mount
      (disch/render-initial! discharge vnode)
      (is @mount-error "Mount callback should have been called")
      ;; Should not throw on unmount
      (disch/apply-child-delta! discharge parent-el
                                 {:delta :remove :path [0] :old-value vnode})
      (is @unmount-error "Unmount callback should have been called"))))
