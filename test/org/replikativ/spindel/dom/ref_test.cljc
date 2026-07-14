(ns org.replikativ.spindel.dom.ref-test
  "Tests for ref callback support in DOM discharge."
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.dom.core :as dom]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.foreign :as foreign]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            #?(:clj [org.replikativ.spindel.test-helpers :as th])))

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
;;
;; These bind an execution context, like every other DOM test — because a
;; foreign node REQUIRES one. They used to call `foreign-node*` bare, and the
;; first test was even named "creates a vnode without context", encoding the bug
;; as intent. A context-free foreign node cannot reconcile its attrs (they froze
;; at mount) and, through the macro, silently dropped its :on-mount/:on-unmount
;; entirely — a div pretending to be an editor.
;; =============================================================================

(defmacro with-ctx
  "Run body with a fresh execution context bound — what a spin always provides."
  [& body]
  `(let [ctx# (ctx/create-execution-context)]
     (binding [ec/*execution-context* ctx#]
       ~@body)))

(deftest test-foreign-node-creation
  (testing "foreign-node builds an ADDRESSED vnode, so its attrs can be reconciled"
    (with-ctx
      (let [mount-calls   (atom [])
            unmount-calls (atom [])
            vnode (foreign/foreign-node*
                   {:file "test" :line 1 :column 1}
                   {:class "editor"
                    :on-mount   (fn [el] (swap! mount-calls conj el))
                    :on-unmount (fn [_] (swap! unmount-calls conj :unmount))})]
        (is (= :div (:tag vnode)))
        (is (= {:class "editor"} @(:attrs vnode)))
        (is (fn? (:ref vnode)))
        (is (some? (:addr vnode))
            "an :addr is what lets the reconciler diff attrs — without it :class
             and :style are frozen at mount, and a foreign host can never be
             hidden instead of unmounted")))))

(deftest test-foreign-node-with-custom-tag
  (testing "foreign-node respects custom tag"
    (with-ctx
      (let [vnode (foreign/foreign-node*
                   {:file "test" :line 1 :column 1}
                   {:tag :pre :class "code"})]
        (is (= :pre (:tag vnode)))))))

(deftest test-foreign-node-mount-callback
  (testing "foreign-node mount callback is called during render"
    (with-ctx
      (let [mount-calls (atom [])
            vnode (foreign/foreign-node*
                   {:file "test" :line 1 :column 1}
                   {:on-mount (fn [el] (swap! mount-calls conj el))})
            {:keys [discharge]} (disch/make-mock-discharge)]
        (disch/render-initial! discharge vnode)
        (is (= 1 (count @mount-calls)))
        (is (some? (first @mount-calls)))))))

(deftest test-foreign-node-unmount-callback
  (testing "foreign-node unmount callback is called on remove"
    (with-ctx
      (let [unmount-calls (atom [])
            vnode (foreign/foreign-node*
                   {:file "test" :line 1 :column 1}
                   {:on-unmount (fn [_] (swap! unmount-calls conj :unmounted))})
            {:keys [discharge]} (disch/make-mock-discharge)
            parent-el :mock-parent]
        (disch/render-initial! discharge vnode)
        (is (empty? @unmount-calls) "Unmount should not be called yet")
        (disch/apply-child-delta! discharge parent-el
                                  {:delta :remove :path [0] :old-value vnode})
        (is (= 1 (count @unmount-calls)))))))

(deftest test-foreign-node-error-handling
  (testing "foreign-node callback errors are caught"
    (with-ctx
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
        (is @unmount-error "Unmount callback should have been called")))))

;; =============================================================================
;; In-place reconciliation tests (Π3)
;;
;; When a `:update` delta has compatible old- and new-vnodes (same
;; :tag, :key, :addr), discharge reuses the existing DOM element and
;; only applies the attribute diff. Refs do NOT re-fire.
;; =============================================================================

(deftest test-update-reconciles-in-place-when-compatible
  (testing "Compatible :update (same tag+key+addr) reuses DOM and does NOT re-fire ref"
    (let [ref-calls (atom [])
          ref-fn (fn [el] (swap! ref-calls conj el))
          old-vnode (-> (dom/make-vnode :div {:ref ref-fn :class "old" :data-x "1"})
                        (assoc :key "k1" :addr ::keyed-child-1))
          new-vnode (-> (dom/make-vnode :div {:ref (fn [el] (swap! ref-calls conj [:new-ref el]))
                                              :class "new"
                                              :data-x "2"})
                        (assoc :key "k1" :addr ::keyed-child-1))
          {:keys [discharge log]} (disch/make-mock-discharge)
          parent-el :mock-parent]
      ;; Initial mount.
      (let [el (disch/render-initial! discharge old-vnode)]
        (is (= 1 (count @ref-calls)) "Initial mount calls ref once")
        (is (= el (first @ref-calls)))
        (reset! ref-calls [])
        (reset! log [])
        ;; Apply :update with compatible vnodes — should reconcile in place.
        (disch/apply-child-delta! discharge parent-el
                                  {:delta :update :path [0]
                                   :old-value old-vnode :value new-vnode})
        ;; Invariant: ref does NOT fire again. Neither old-ref(nil) nor new-ref(el).
        (is (empty? @ref-calls)
            "In-place reconciliation must not call ref")
        ;; Attribute updates were applied to the same element.
        (let [set-class (filter #(and (= :set-attr (:op %)) (= :class (:attr %))) @log)
              set-data-x (filter #(and (= :set-attr (:op %)) (= :data-x (:attr %))) @log)]
          (is (some #(= "new" (:value %)) set-class)
              "Class attribute updated to 'new'")
          (is (some #(= "2" (:value %)) set-data-x)
              "data-x attribute updated to '2'"))
        ;; No replace-child was issued — the DOM element survived.
        (is (empty? (filter #(= :replace-child (:op %)) @log))
            "No replace-child for compatible :update")))))

#?(:clj
   (deftest test-update-falls-back-when-tag-differs
     (testing "Incompatible :update (different tag) destroys + recreates and DOES fire ref"
       (th/with-ctx [_ctx]
         (let [old-calls (atom [])
               new-calls (atom [])
               old-vnode (-> (dom/make-vnode :div {:ref (fn [el] (swap! old-calls conj el))})
                             (assoc :addr ::tag-old))
               new-vnode (-> (dom/make-vnode :span {:ref (fn [el] (swap! new-calls conj el))})
                             (assoc :addr ::tag-old))
               {:keys [discharge]} (disch/make-mock-discharge)
               parent-el :mock-parent]
           (disch/render-initial! discharge old-vnode)
           (reset! old-calls [])
           (reset! new-calls [])
           (disch/apply-child-delta! discharge parent-el
                                     {:delta :update :path [0]
                                      :old-value old-vnode :value new-vnode})
           (is (= [nil] @old-calls)
               "Old ref fires with nil (unmount) because tags differ")
           (is (= 1 (count @new-calls))
               "New ref fires with the new element"))))))

(deftest test-many-updates-fire-ref-exactly-once
  (testing "Across N compatible :update cycles with same tag+key+addr, ref fires exactly once"
    (let [n 50
          ref-calls (atom 0)
          ref-fn (fn [_el] (swap! ref-calls inc))
          mk (fn [i]
               (-> (dom/make-vnode :div {:ref ref-fn :data-i (str i)})
                   (assoc :key "stable" :addr ::stable-child)))
          v0 (mk 0)
          {:keys [discharge]} (disch/make-mock-discharge)
          parent-el :mock-parent]
      (disch/render-initial! discharge v0)
      (is (= 1 @ref-calls) "Initial mount fires ref once")
      ;; Apply N updates with the same tag/key/addr.
      (loop [i 1 prev v0]
        (when (<= i n)
          (let [nxt (mk i)]
            (disch/apply-child-delta! discharge parent-el
                                      {:delta :update :path [0]
                                       :old-value prev :value nxt})
            (recur (inc i) nxt))))
      (is (= 1 @ref-calls)
          "After N in-place reconciliations, ref has still only fired once"))))
