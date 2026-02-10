(ns org.replikativ.spindel.dom.router-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.dom.router :as router #?(:clj :refer :cljs :refer-macros) [router link]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
            #?(:clj [org.replikativ.spindel.test-async :refer [await-drain]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; Query String Tests
;; =============================================================================

(deftest test-parse-query-string
  (testing "Basic key=value pairs"
    (is (= {:foo "bar" :baz "qux"}
           (router/parse-query-string "foo=bar&baz=qux"))))

  (testing "Single pair"
    (is (= {:tab "posts"}
           (router/parse-query-string "tab=posts"))))

  (testing "Empty string returns empty map"
    (is (= {} (router/parse-query-string ""))))

  (testing "Nil returns empty map"
    (is (= {} (router/parse-query-string nil))))

  (testing "URL-encoded values"
    (is (= {:q "hello world"}
           (router/parse-query-string "q=hello+world"))))

  (testing "Key with empty value"
    (is (= {:flag ""}
           (router/parse-query-string "flag=")))))

(deftest test-build-query-string
  (testing "Basic map to query string"
    (let [qs (router/build-query-string {:foo "bar"})]
      (is (= "foo=bar" qs))))

  (testing "Empty map returns nil"
    (is (nil? (router/build-query-string {}))))

  (testing "Nil returns nil"
    (is (nil? (router/build-query-string nil))))

  (testing "Multiple params"
    (let [qs (router/build-query-string {:a "1" :b "2"})]
      ;; Order may vary, so check both parts exist
      (is (string? qs))
      (is (or (= "a=1&b=2" qs) (= "b=2&a=1" qs))))))

;; =============================================================================
;; Route Compilation Tests
;; =============================================================================

(deftest test-compile-routes
  (testing "Simple static routes"
    (let [routes (router/compile-routes [["/" :home] ["/about" :about]])]
      (is (= 2 (count routes)))
      (is (= :home (:name (first routes))))
      (is (= :about (:name (second routes))))
      (is (= [] (:segments (first routes))))
      (is (= false (:wildcard? (first routes))))))

  (testing "Parameterized route"
    (let [routes (router/compile-routes [["/users/:id" :user]])]
      (is (= 1 (count routes)))
      (is (= :user (:name (first routes))))
      (is (= [:id] (:param-names (first routes))))
      (is (= 2 (count (:segments (first routes)))))
      (is (= :literal (:type (first (:segments (first routes))))))
      (is (= :param (:type (second (:segments (first routes))))))))

  (testing "Multi-param route"
    (let [routes (router/compile-routes [["/users/:id/posts/:post-id" :user-post]])]
      (is (= [:id :post-id] (:param-names (first routes))))))

  (testing "Wildcard route"
    (let [routes (router/compile-routes [["/*rest" :not-found]])]
      (is (= true (:wildcard? (first routes)))))))

;; =============================================================================
;; Route Matching Tests
;; =============================================================================

(def test-routes
  (router/compile-routes
    [["/" :home]
     ["/about" :about]
     ["/users/:id" :user]
     ["/users/:id/posts/:post-id" :user-post]
     ["/*rest" :not-found]]))

(deftest test-match-route-exact
  (testing "Root path"
    (let [result (router/match-route test-routes "/")]
      (is (= :home (:name result)))
      (is (= "/" (:path result)))
      (is (= {} (:path-params result)))
      (is (= {} (:query-params result)))))

  (testing "Static path"
    (let [result (router/match-route test-routes "/about")]
      (is (= :about (:name result)))
      (is (= "/about" (:path result))))))

(deftest test-match-route-params
  (testing "Single param"
    (let [result (router/match-route test-routes "/users/42")]
      (is (= :user (:name result)))
      (is (= "/users/42" (:path result)))
      (is (= {:id "42"} (:path-params result)))))

  (testing "Multiple params"
    (let [result (router/match-route test-routes "/users/42/posts/7")]
      (is (= :user-post (:name result)))
      (is (= {:id "42" :post-id "7"} (:path-params result))))))

(deftest test-match-route-query-params
  (testing "Path with query string"
    (let [result (router/match-route test-routes "/users/42?tab=posts")]
      (is (= :user (:name result)))
      (is (= "/users/42" (:path result)))
      (is (= {:id "42"} (:path-params result)))
      (is (= {:tab "posts"} (:query-params result)))))

  (testing "Multiple query params"
    (let [result (router/match-route test-routes "/about?ref=nav&lang=en")]
      (is (= :about (:name result)))
      (is (= {:ref "nav" :lang "en"} (:query-params result))))))

(deftest test-match-route-wildcard
  (testing "Wildcard catches unmatched paths"
    (let [result (router/match-route test-routes "/something/unknown")]
      (is (= :not-found (:name result)))
      (is (= {:rest "something/unknown"} (:path-params result))))))

(deftest test-match-route-no-match
  (testing "No match without wildcard returns nil name"
    (let [routes (router/compile-routes [["/" :home] ["/about" :about]])
          result (router/match-route routes "/unknown")]
      (is (nil? (:name result)))
      (is (= "/unknown" (:path result))))))

;; =============================================================================
;; Reverse Routing Tests
;; =============================================================================

(deftest test-path-for
  (testing "Static route"
    (is (= "/" (router/path-for test-routes :home {})))
    (is (= "/about" (router/path-for test-routes :about {}))))

  (testing "Parameterized route"
    (is (= "/users/123" (router/path-for test-routes :user {:id "123"}))))

  (testing "Multi-param route"
    (is (= "/users/42/posts/7"
           (router/path-for test-routes :user-post {:id "42" :post-id "7"}))))

  (testing "Unknown route throws"
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs ExceptionInfo)
                 (router/path-for test-routes :nonexistent {}))))

  (testing "Missing param throws"
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs ExceptionInfo)
                 (router/path-for test-routes :user {})))))

;; =============================================================================
;; Router + Signal Integration Tests
;; =============================================================================

#?(:clj
   (deftest test-router-creation
     (testing "Router creates with initial route from default path"
       (with-ctx [ctx]
         (let [r (router [["/" :home] ["/about" :about]])]
           (is (some? r))
           (is (= :home (:name @(:signal r))))
           (is (= "/" (:path @(:signal r)))))))

     (testing "Router creates with initial route from explicit path"
       (with-ctx [ctx]
         (let [r (router [["/" :home] ["/users/:id" :user]]
                         {:path "/users/42?tab=posts"})]
           (is (= :user (:name @(:signal r))))
           (is (= "/users/42" (:path @(:signal r))))
           (is (= {:id "42"} (:path-params @(:signal r))))
           (is (= {:tab "posts"} (:query-params @(:signal r)))))))))

#?(:clj
   (deftest test-router-navigate
     (testing "navigate! updates signal"
       (with-ctx [ctx]
         (let [r (router [["/" :home] ["/about" :about] ["/users/:id" :user]])]
           (is (= :home (:name @(:signal r))))
           (router/navigate! r "/about")
           (is (= :about (:name @(:signal r))))
           (is (= "/about" (:path @(:signal r)))))))

     (testing "navigate! by route name"
       (with-ctx [ctx]
         (let [r (router [["/" :home] ["/users/:id" :user]])]
           (router/navigate! r :user {:id "99"})
           (is (= :user (:name @(:signal r))))
           (is (= {:id "99"} (:path-params @(:signal r)))))))

     (testing "navigate! with query params"
       (with-ctx [ctx]
         (let [r (router [["/" :home] ["/users/:id" :user]])]
           (router/navigate! r :user {:id "1"} {:tab "posts"})
           (is (= :user (:name @(:signal r))))
           (is (= {:tab "posts"} (:query-params @(:signal r)))))))))

#?(:clj
   (deftest test-router-replace
     (testing "replace! updates signal"
       (with-ctx [ctx]
         (let [r (router [["/" :home] ["/about" :about]])]
           (router/replace! r "/about")
           (is (= :about (:name @(:signal r)))))))))

;; =============================================================================
;; Href Tests
;; =============================================================================

#?(:clj
   (deftest test-href
     (testing "Generate path from route name"
       (with-ctx [ctx]
         (let [r (router [["/" :home] ["/users/:id" :user]])]
           (is (= "/users/123" (router/href r :user {:id "123"}))))))

     (testing "Generate path with query params"
       (with-ctx [ctx]
         (let [r (router [["/" :home] ["/users/:id" :user]])]
           (is (= "/users/1?q=hi" (router/href r :user {:id "1"} {:q "hi"}))))))))

;; =============================================================================
;; Reactive Integration Tests
;; =============================================================================

#?(:clj
   (deftest test-router-reactive-tracking
     (testing "Spin tracks router signal reactively"
       (with-ctx [ctx]
         (let [r (router [["/" :home] ["/about" :about] ["/users/:id" :user]])
               route-name-spin (spin
                                 (let [{:keys [new]} (track (:signal r))]
                                   (:name new)))]
           (is (= :home @route-name-spin))
           (router/navigate! r "/about")
           (await-drain ctx)
           (is (= :about @route-name-spin))
           (router/navigate! r :user {:id "42"})
           (await-drain ctx)
           (is (= :user @route-name-spin)))))))
