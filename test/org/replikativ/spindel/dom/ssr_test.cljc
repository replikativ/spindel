(ns org.replikativ.spindel.dom.ssr-test
  (:require #?(:clj [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer-macros [deftest is testing use-fixtures]])
            [org.replikativ.spindel.dom.ssr :as ssr]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.core :as dom]
            [org.replikativ.spindel.dom.fragment :as frag]
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
;; Basic Element Rendering
;; =============================================================================

(deftest test-empty-element
  (is (= "<div></div>" (ssr/render-to-string (el/div)))))

(deftest test-element-with-attrs
  (is (= "<div class=\"x\" id=\"main\"></div>"
         (ssr/render-to-string (el/div {:class "x" :id "main"})))))

(deftest test-text-children
  (is (= "<p>hello</p>" (ssr/render-to-string (el/p "hello")))))

(deftest test-multiple-text-children
  (is (= "<p>ab</p>" (ssr/render-to-string (el/p "a" "b")))))

(deftest test-nested-elements
  (is (= "<div><span>hi</span></div>"
         (ssr/render-to-string (el/div (el/span "hi"))))))

(deftest test-deeply-nested
  (is (= "<div><section><p><strong>deep</strong></p></section></div>"
         (ssr/render-to-string
          (el/div (el/section (el/p (el/strong "deep"))))))))

;; =============================================================================
;; Void Elements
;; =============================================================================

(deftest test-void-br
  (is (= "<br />" (ssr/render-to-string (el/br)))))

(deftest test-void-img
  (is (= "<img src=\"x.png\" />"
         (ssr/render-to-string (el/img {:src "x.png"})))))

(deftest test-void-input
  (is (= "<input type=\"text\" />"
         (ssr/render-to-string (el/input {:type "text"})))))

(deftest test-void-hr
  (is (= "<hr />" (ssr/render-to-string (el/hr)))))

;; =============================================================================
;; HTML Escaping
;; =============================================================================

(deftest test-escape-text-content
  (is (= "<p>&lt;script&gt;alert(&#x27;xss&#x27;)&lt;/script&gt;</p>"
         (ssr/render-to-string (el/p "<script>alert('xss')</script>")))))

(deftest test-escape-attr-value
  (is (= "<div class=\"a&amp;b&quot;c\"></div>"
         (ssr/render-to-string (el/div {:class "a&b\"c"})))))

;; =============================================================================
;; Boolean & Special Attributes
;; =============================================================================

(deftest test-boolean-true-attr
  (is (= "<input disabled />"
         (ssr/render-to-string (el/input {:disabled true})))))

(deftest test-boolean-false-attr
  (is (= "<input />"
         (ssr/render-to-string (el/input {:disabled false})))))

(deftest test-nil-attr-skipped
  (is (= "<div></div>"
         (ssr/render-to-string (el/div {:class nil})))))

(deftest test-event-handler-skipped
  (is (= "<button>Go</button>"
         (ssr/render-to-string (el/button {:on-click (fn [_])} "Go")))))

;; =============================================================================
;; Fragments
;; =============================================================================

(deftest test-fragment
  (is (= "<span>a</span><span>b</span>"
         (ssr/render-to-string (el/fragment (el/span "a") (el/span "b"))))))

(deftest test-keyed-fragment
  (is (= "<li>1</li><li>2</li>"
         (ssr/render-to-string
          (frag/keyed-fragment [(el/li "1") (el/li "2")])))))

;; =============================================================================
;; Nil Handling
;; =============================================================================

(deftest test-nil-renders-empty
  (is (= "" (ssr/render-to-string nil))))

(deftest test-nil-children-skipped
  (is (= "<ul><li>a</li><li>b</li></ul>"
         (ssr/render-to-string
          (dom/make-vnode :ul {}
                          [(el/li "a") nil (el/li "b")])))))

;; =============================================================================
;; render-to-string-fragment
;; =============================================================================

(deftest test-render-to-string-fragment
  (is (= "<h1>Title</h1><p>Body</p>"
         (ssr/render-to-string-fragment
          [(el/h1 "Title") (el/p "Body")]))))

;; =============================================================================
;; Document Structure (SSR use case)
;; =============================================================================

(deftest test-full-page
  (is (= "<html><head><title>Test</title></head><body><div>Hello</div></body></html>"
         (ssr/render-to-string
          (el/html
           (el/head (el/title "Test"))
           (el/body (el/div "Hello")))))))

;; =============================================================================
;; Edge Cases
;; =============================================================================

(deftest test-number-attr-value
  (is (= "<div tabindex=\"0\"></div>"
         (ssr/render-to-string (el/div {:tabindex 0})))))

(deftest test-text-node-directly
  (is (= "hello" (ssr/render-to-string (dom/make-text-vnode "hello")))))

(deftest test-empty-fragment
  (is (= "" (ssr/render-to-string (el/fragment)))))
