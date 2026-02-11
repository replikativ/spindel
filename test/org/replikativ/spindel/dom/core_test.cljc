(ns org.replikativ.spindel.dom.core-test
  (:require #?(:clj [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer-macros [deftest is testing use-fixtures]])
            [org.replikativ.spindel.dom.core :as dom]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]))

(use-fixtures :each
  (fn [f]
    (let [test-ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* test-ctx]
          (f))
        (finally
          (ctx/stop-context! test-ctx))))))

;; =============================================================================
;; VNode Creation Tests
;; =============================================================================

(deftest test-make-vnode
  (testing "Basic vnode creation"
    (let [v (dom/make-vnode :div {:class "test"})]
      (is (= :div (:tag v)))
      (is (= {:class "test"} @(:attrs v)))
      (is (= [] @(:children v)))
      (is (nil? (:key v)))))

  (testing "Vnode with key"
    (let [v (dom/make-vnode :li {:key "item-1" :class "item"})]
      (is (= "item-1" (:key v)))
      (is (= {:class "item"} @(:attrs v)))))

  (testing "Vnode with children"
    (let [child (dom/make-text-vnode "Hello")
          v (dom/make-vnode :div {} [child])]
      (is (= 1 (count @(:children v))))
      (is (= child (first @(:children v))))))

  (testing "Vnode with ref callback"
    (let [ref-fn (fn [_el] nil)
          v (dom/make-vnode :div {:ref ref-fn})]
      (is (= ref-fn (:ref v)))
      (is (= {} @(:attrs v))))))

(deftest test-make-text-vnode
  (testing "Text node creation"
    (let [t (dom/make-text-vnode "Hello")]
      (is (= :text (:tag t)))
      (is (= "Hello" (:content t)))))

  (testing "Text node with number"
    (let [t (dom/make-text-vnode 42)]
      (is (= "42" (:content t))))))

(deftest test-make-fragment-vnode
  (testing "Empty fragment"
    (let [f (dom/make-fragment-vnode)]
      (is (dom/fragment? f))
      (is (= [] @(:children f)))))

  (testing "Fragment with children"
    (let [f (dom/make-fragment-vnode [(dom/make-text-vnode "A")
                                       (dom/make-text-vnode "B")])]
      (is (= 2 (count @(:children f)))))))

;; =============================================================================
;; VNode Predicates Tests
;; =============================================================================

(deftest test-predicates
  (testing "vnode?"
    (is (dom/vnode? (dom/make-vnode :div {})))
    (is (dom/vnode? (dom/make-text-vnode "hi")))
    (is (not (dom/vnode? "string")))
    (is (not (dom/vnode? nil))))

  (testing "text-node?"
    (is (dom/text-node? (dom/make-text-vnode "hi")))
    (is (not (dom/text-node? (dom/make-vnode :div {})))))

  (testing "fragment?"
    (is (dom/fragment? (dom/make-fragment-vnode)))
    (is (not (dom/fragment? (dom/make-vnode :div {})))))

  (testing "element-node?"
    (is (dom/element-node? (dom/make-vnode :div {})))
    (is (not (dom/element-node? (dom/make-text-vnode "hi"))))
    (is (not (dom/element-node? (dom/make-fragment-vnode))))))

;; =============================================================================
;; Immutable Update Tests
;; =============================================================================

(deftest test-update-attrs
  (testing "Add new attribute"
    (let [v1 (dom/make-vnode :div {:class "original"})
          ;; Clear initial deltas so we only see update deltas
          v1-cleared (dom/clear-deltas v1)
          v2 (dom/update-attrs v1-cleared {:class "original" :id "new"})]
      (is (= {:class "original" :id "new"} @(:attrs v2)))
      ;; Original unchanged
      (is (= {:class "original"} @(:attrs v1-cleared)))
      ;; Only the :id add should be tracked (class unchanged)
      (let [deltas (d/get-deltas (:attrs v2))]
        (is (= 1 (count deltas)))
        (is (= :add (:delta (first deltas))))
        (is (= [:id] (:path (first deltas)))))))

  (testing "Update existing attribute"
    (let [v1 (dom/make-vnode :div {:class "original"})
          v1-cleared (dom/clear-deltas v1)
          v2 (dom/update-attrs v1-cleared {:class "updated"})]
      (is (= {:class "updated"} @(:attrs v2)))
      (let [deltas (d/get-deltas (:attrs v2))]
        (is (= 1 (count deltas)))
        (is (= :update (:delta (first deltas))))
        (is (= "original" (:old-value (first deltas)))))))

  (testing "Remove attribute"
    (let [v1 (dom/make-vnode :div {:class "test" :id "remove-me"})
          v1-cleared (dom/clear-deltas v1)
          v2 (dom/update-attrs v1-cleared {:class "test"})]
      (is (= {:class "test"} @(:attrs v2)))
      (let [deltas (d/get-deltas (:attrs v2))]
        (is (some #(= :remove (:delta %)) deltas))))))

(deftest test-append-child
  (testing "Append single child"
    (let [v1 (dom/make-vnode :div {})
          v2 (dom/append-child v1 (dom/make-text-vnode "Hello"))]
      (is (= 1 (count @(:children v2))))
      (is (= 0 (count @(:children v1))))
      (let [deltas (d/get-deltas (:children v2))]
        (is (= 1 (count deltas)))
        (is (= :add (:delta (first deltas))))
        (is (= [0] (:path (first deltas)))))))

  (testing "Append multiple children"
    (let [v1 (dom/make-vnode :div {})
          v2 (-> v1
                 (dom/append-child (dom/make-text-vnode "A"))
                 (dom/append-child (dom/make-text-vnode "B"))
                 (dom/append-child (dom/make-text-vnode "C")))]
      (is (= 3 (count @(:children v2))))
      (let [deltas (d/get-deltas (:children v2))]
        (is (= 3 (count deltas)))
        (is (= [[0] [1] [2]] (mapv :path deltas)))))))

(deftest test-update-child
  (testing "Update child at index"
    (let [v1 (dom/make-vnode :div {} [(dom/make-text-vnode "Old")])
          v2 (dom/update-child v1 0 (dom/make-text-vnode "New"))]
      (is (= "New" (:content (first @(:children v2)))))
      (let [deltas (d/get-deltas (:children v2))]
        (is (= 1 (count deltas)))
        (is (= :update (:delta (first deltas))))))))

(deftest test-remove-child-at
  (testing "Remove child at index"
    (let [v1 (dom/make-vnode :div {} [(dom/make-text-vnode "A")
                                       (dom/make-text-vnode "B")
                                       (dom/make-text-vnode "C")])
          v2 (dom/remove-child-at v1 1)]
      (is (= 2 (count @(:children v2))))
      (is (= "A" (:content (first @(:children v2)))))
      (is (= "C" (:content (second @(:children v2))))))))

;; =============================================================================
;; Path-Based Update Tests
;; =============================================================================

(deftest test-get-in-vdom
  (testing "Get nested vnode"
    (let [inner (dom/make-text-vnode "Deep")
          middle (dom/make-vnode :span {} [inner])
          outer (dom/make-vnode :div {} [middle])]
      (is (= middle (dom/get-in-vdom outer [0])))
      (is (= inner (dom/get-in-vdom outer [0 0]))))))

(deftest test-update-in-vdom
  (testing "Update nested vnode"
    (let [inner (dom/make-text-vnode "Old")
          middle (dom/make-vnode :span {} [inner])
          outer (dom/make-vnode :div {} [middle])
          updated (dom/update-in-vdom outer [0 0]
                    (constantly (dom/make-text-vnode "New")))]
      (is (= "New" (:content (dom/get-in-vdom updated [0 0]))))
      ;; Original unchanged
      (is (= "Old" (:content (dom/get-in-vdom outer [0 0])))))))

;; =============================================================================
;; Delta Extraction Tests
;; =============================================================================

(deftest test-has-deltas
  (testing "Fresh vnode with cleared deltas has no deltas"
    (let [v (dom/make-vnode :div {:class "test"})
          v-cleared (dom/clear-deltas v)]
      (is (not (dom/has-deltas? v-cleared)))))

  (testing "Fresh vnode has no deltas (deltaable starts empty)"
    ;; deltaable-map/vector are created with initial values,
    ;; but those are not recorded as deltas
    (let [v (dom/make-vnode :div {:class "test"})]
      (is (not (dom/has-deltas? v)))))

  (testing "Modified vnode has deltas"
    (let [v1 (dom/make-vnode :div {:class "a"})
          v1-cleared (dom/clear-deltas v1)
          v2 (dom/update-attrs v1-cleared {:class "b"})]
      (is (dom/has-deltas? v2)))))

(deftest test-clear-deltas
  (testing "Clear deltas from single node"
    (let [v1 (dom/make-vnode :div {:class "a"})
          v1-cleared (dom/clear-deltas v1)
          v2 (dom/update-attrs v1-cleared {:class "b"})
          v3 (dom/clear-deltas v2)]
      (is (dom/has-deltas? v2))
      (is (not (dom/has-deltas? v3)))
      ;; Value unchanged
      (is (= {:class "b"} @(:attrs v3))))))

;; =============================================================================
;; Element Helper Tests
;; =============================================================================

(deftest test-element-helpers
  (testing "div with attrs and children"
    (let [v (el/div {:class "container"}
                    (el/span "Hello")
                    (el/span "World"))]
      (is (= :div (:tag v)))
      (is (= {:class "container"} @(:attrs v)))
      (is (= 2 (count @(:children v))))))

  (testing "div without attrs"
    (let [v (el/div (el/span "Hi"))]
      (is (= :div (:tag v)))
      (is (= {} @(:attrs v)))
      (is (= 1 (count @(:children v))))))

  (testing "Nested elements"
    (let [v (el/ul {:class "list"}
                   (el/li {:key "1"} "Item 1")
                   (el/li {:key "2"} "Item 2"))]
      (is (= :ul (:tag v)))
      (is (= 2 (count @(:children v))))
      (is (= "1" (:key (first @(:children v)))))))

  (testing "Text coercion"
    (let [v (el/p "Hello " 42 " times")]
      (is (= 3 (count @(:children v))))
      (is (every? dom/text-node? @(:children v)))))

  (testing "Sequence flattening"
    ;; Note: Since elements are macros, can't pass directly to map.
    ;; Use (fn [x] (el/li x)) instead, or wrap in a sequence.
    (let [items ["A" "B" "C"]
          v (el/ul (map (fn [item] (el/li item)) items))]
      (is (= 3 (count @(:children v)))))))

;; =============================================================================
;; Discharge Tests
;; =============================================================================

(deftest test-mock-discharge-initial-render
  (testing "Initial render creates all elements"
    (let [{:keys [discharge log]} (disch/make-mock-discharge)
          app (el/div {:class "app"}
                      (el/h1 "Title")
                      (el/p "Content"))]
      (disch/render-initial! discharge app)
      (let [ops @log]
        ;; Should create div, h1, text, p, text
        (is (= 3 (count (filter #(= :create-element (:op %)) ops))))
        (is (= 2 (count (filter #(= :create-text (:op %)) ops))))
        ;; Should set class attribute
        (is (some #(and (= :set-attr (:op %))
                        (= :class (:attr %))) ops))))))

(deftest test-keyed-children
  (testing "Children with keys"
    (let [v (el/ul
              (el/li {:key "a"} "A")
              (el/li {:key "b"} "B")
              (el/li {:key "c"} "C"))
          indexed (dom/children-by-key @(:children v))]
      (is (= 3 (count (:by-key indexed))))
      (is (contains? (:by-key indexed) "a"))
      (is (contains? (:by-key indexed) "b"))
      (is (contains? (:by-key indexed) "c")))))

;; =============================================================================
;; Addressing Tests
;; =============================================================================

(deftest test-keyed-address
  (testing "Keyed address is deterministic"
    (let [addr1 (dom/keyed-address :base-addr "item-1")
          addr2 (dom/keyed-address :base-addr "item-1")
          addr3 (dom/keyed-address :base-addr "item-2")]
      (is (= addr1 addr2))
      (is (not= addr1 addr3)))))

(deftest test-next-address
  (testing "Address chain evolution"
    (let [[addr1 chain1] (dom/next-address nil "el" {:line 1})
          [addr2 chain2] (dom/next-address chain1 "el" {:line 2})
          [addr3 _] (dom/next-address chain2 "el" {:line 1})]
      ;; All addresses are different
      (is (not= addr1 addr2))
      (is (not= addr2 addr3))
      ;; Same source-loc + chain gives same address
      (let [[addr1-again _] (dom/next-address nil "el" {:line 1})]
        (is (= addr1 addr1-again))))))
