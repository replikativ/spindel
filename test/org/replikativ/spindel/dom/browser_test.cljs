(ns org.replikativ.spindel.dom.browser-test
  "Tests for browser DOM discharge using jsdom."
  (:require [cljs.test :refer-macros [deftest is testing]]
            [org.replikativ.spindel.dom.core :as dom]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.browser :as browser]
            ["jsdom" :refer [JSDOM]]))

;; =============================================================================
;; Test Helpers
;; =============================================================================

(defn make-test-document
  "Create a fresh jsdom document for testing."
  []
  (let [jsdom (JSDOM. "<!DOCTYPE html><html><body></body></html>")]
    (.-document (.-window jsdom))))

(defn get-body [doc]
  (.-body doc))

;; =============================================================================
;; Basic Rendering Tests
;; =============================================================================

(deftest test-render-simple-element
  (testing "Render a simple div"
    (let [doc (make-test-document)
          body (get-body doc)
          vdom (el/div {:id "test"} "Hello")
          discharge (browser/mount! body vdom)
          rendered (.-firstChild body)]
      (is (some? rendered))
      (is (= "DIV" (.-tagName rendered)))
      (is (= "test" (.getAttribute rendered "id")))
      (is (= "Hello" (.-textContent rendered))))))

(deftest test-render-nested-elements
  (testing "Render nested structure"
    (let [doc (make-test-document)
          body (get-body doc)
          vdom (el/div {:class "container"}
                       (el/h1 "Title")
                       (el/p "Paragraph"))
          _ (browser/mount! body vdom)
          container (.-firstChild body)
          children (.-children container)]
      (is (= "DIV" (.-tagName container)))
      (is (= "container" (.getAttribute container "class")))
      (is (= 2 (.-length children)))
      (is (= "H1" (.-tagName (aget children 0))))
      (is (= "P" (.-tagName (aget children 1)))))))

(deftest test-render-list
  (testing "Render a list with items"
    (let [doc (make-test-document)
          body (get-body doc)
          vdom (el/ul {:class "list"}
                      (el/li {:key "1"} "Item 1")
                      (el/li {:key "2"} "Item 2")
                      (el/li {:key "3"} "Item 3"))
          _ (browser/mount! body vdom)
          ul (.-firstChild body)
          items (.-children ul)]
      (is (= "UL" (.-tagName ul)))
      (is (= 3 (.-length items)))
      (is (= "Item 1" (.-textContent (aget items 0))))
      (is (= "Item 2" (.-textContent (aget items 1))))
      (is (= "Item 3" (.-textContent (aget items 2)))))))

;; =============================================================================
;; Attribute Tests
;; =============================================================================

(deftest test-set-attributes
  (testing "Various attribute types"
    (let [doc (make-test-document)
          body (get-body doc)
          vdom (el/input {:type "text"
                          :id "my-input"
                          :class "form-control"
                          :disabled true
                          :placeholder "Enter text"})
          _ (browser/mount! body vdom)
          input (.-firstChild body)]
      (is (= "INPUT" (.-tagName input)))
      (is (= "text" (.getAttribute input "type")))
      (is (= "my-input" (.getAttribute input "id")))
      (is (= "form-control" (.getAttribute input "class")))
      (is (.hasAttribute input "disabled"))
      (is (= "Enter text" (.getAttribute input "placeholder"))))))

(deftest test-boolean-attributes
  (testing "Boolean attributes handled correctly"
    (let [doc (make-test-document)
          body (get-body doc)]
      ;; Test true boolean
      (let [vdom (el/input {:disabled true})
            _ (browser/mount! body vdom)
            input (.-firstChild body)]
        (is (.hasAttribute input "disabled")))

      ;; Clear and test false boolean
      (set! (.-innerHTML body) "")
      (let [vdom (el/input {:disabled false})
            _ (browser/mount! body vdom)
            input (.-firstChild body)]
        (is (not (.hasAttribute input "disabled")))))))

;; =============================================================================
;; Text Node Tests
;; =============================================================================

(deftest test-text-nodes
  (testing "Text nodes rendered correctly"
    (let [doc (make-test-document)
          body (get-body doc)
          vdom (el/p "Hello " "World" "!")
          _ (browser/mount! body vdom)
          p (.-firstChild body)]
      (is (= "Hello World!" (.-textContent p)))
      ;; Should have 3 text nodes as children
      (is (= 3 (.-length (.-childNodes p)))))))

(deftest test-numeric-text
  (testing "Numbers converted to text"
    (let [doc (make-test-document)
          body (get-body doc)
          vdom (el/span "Count: " 42)
          _ (browser/mount! body vdom)
          span (.-firstChild body)]
      (is (= "Count: 42" (.-textContent span))))))

;; =============================================================================
;; Delta Update Tests
;; =============================================================================

(deftest test-attribute-delta-update
  (testing "Attribute updates via delta discharge"
    (let [doc (make-test-document)
          body (get-body doc)
          ;; Initial render
          v1 (el/div {:class "old" :id "test"})
          discharge (browser/mount! body v1)
          div (.-firstChild body)]
      ;; Verify initial state
      (is (= "old" (.getAttribute div "class")))
      (is (= "test" (.getAttribute div "id")))

      ;; Update attributes (simulating what would happen in real usage)
      ;; First clear deltas from initial render
      (let [v1-cleared (dom/clear-deltas v1)
            ;; Then update attributes
            v2 (dom/update-attrs v1-cleared {:class "new" :id "test"})]
        ;; Re-store element reference for v2
        (disch/set-element! discharge v2 div)
        ;; Apply deltas
        (disch/discharge-vnode! discharge v2)
        ;; Verify update
        (is (= "new" (.getAttribute div "class")))
        (is (= "test" (.getAttribute div "id")))))))

(deftest test-attribute-removal
  (testing "Attributes removed via delta"
    (let [doc (make-test-document)
          body (get-body doc)
          v1 (el/div {:class "test" :data-foo "bar"})
          discharge (browser/mount! body v1)
          div (.-firstChild body)]
      ;; Verify initial state
      (is (= "bar" (.getAttribute div "data-foo")))

      ;; Remove data-foo attribute
      (let [v1-cleared (dom/clear-deltas v1)
            v2 (dom/update-attrs v1-cleared {:class "test"})]
        (disch/set-element! discharge v2 div)
        (disch/discharge-vnode! discharge v2)
        ;; Attribute should be removed
        (is (not (.hasAttribute div "data-foo")))
        (is (= "test" (.getAttribute div "class")))))))

;; =============================================================================
;; Child Update Tests
;; =============================================================================

(deftest test-append-child-delta
  (testing "Append child via delta"
    (let [doc (make-test-document)
          body (get-body doc)
          v1 (el/ul (el/li "Item 1"))
          discharge (browser/mount! body v1)
          ul (.-firstChild body)]
      (is (= 1 (.-length (.-children ul))))

      ;; Append a new child
      (let [v1-cleared (dom/clear-deltas v1)
            v2 (dom/append-child v1-cleared (el/li "Item 2"))]
        (disch/set-element! discharge v2 ul)
        (disch/discharge-vnode! discharge v2)
        (is (= 2 (.-length (.-children ul))))
        (is (= "Item 2" (.-textContent (aget (.-children ul) 1))))))))

;; =============================================================================
;; HTML Output Tests
;; =============================================================================

(deftest test-html-output
  (testing "Get HTML representation"
    (let [doc (make-test-document)
          body (get-body doc)
          vdom (el/div {:id "app"}
                       (el/span "Content"))
          _ (browser/mount! body vdom)
          div (.-firstChild body)]
      (is (= "<span>Content</span>" (browser/get-html div)))
      (is (= "<div id=\"app\"><span>Content</span></div>"
             (browser/get-outer-html div))))))

;; =============================================================================
;; Complex Structure Tests
;; =============================================================================

(deftest test-complex-structure
  (testing "Complex nested structure"
    (let [doc (make-test-document)
          body (get-body doc)
          vdom (el/div {:class "app"}
                       (el/header {:class "header"}
                                  (el/h1 "My App")
                                  (el/nav (el/a {:href "/"} "Home")
                                          (el/a {:href "/about"} "About")))
                       (el/main {:class "content"}
                                (el/article
                                  (el/h2 "Article Title")
                                  (el/p "Article content...")))
                       (el/footer {:class "footer"}
                                  (el/p "© 2024")))
          _ (browser/mount! body vdom)
          app (.-firstChild body)]
      ;; Verify structure
      (is (= "DIV" (.-tagName app)))
      (is (= "app" (.getAttribute app "class")))

      (let [children (.-children app)]
        (is (= 3 (.-length children)))
        (is (= "HEADER" (.-tagName (aget children 0))))
        (is (= "MAIN" (.-tagName (aget children 1))))
        (is (= "FOOTER" (.-tagName (aget children 2))))))))

(deftest test-table-structure
  (testing "Table with rows and cells"
    (let [doc (make-test-document)
          body (get-body doc)
          vdom (el/table {:class "data-table"}
                         (el/thead
                           (el/tr
                             (el/th "Name")
                             (el/th "Value")))
                         (el/tbody
                           (el/tr {:key "1"}
                                  (el/td "A")
                                  (el/td "100"))
                           (el/tr {:key "2"}
                                  (el/td "B")
                                  (el/td "200"))))
          _ (browser/mount! body vdom)
          table (.-firstChild body)]
      (is (= "TABLE" (.-tagName table)))
      (let [thead (aget (.-children table) 0)
            tbody (aget (.-children table) 1)]
        (is (= "THEAD" (.-tagName thead)))
        (is (= "TBODY" (.-tagName tbody)))
        (is (= 2 (.-length (.-children tbody))))))))
