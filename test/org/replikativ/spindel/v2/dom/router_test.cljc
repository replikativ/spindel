(ns org.replikativ.spindel.v2.dom.router-test
  "The router on engine v2: route matching and reverse routing (pure,
   ported from dom/router_test), the route signal in the router's world,
   navigation, and `link` rendered through a mount: a click navigates and
   the mount commits the new route."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.dom.router :as router :refer [link]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

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
;; The route signal
;; =============================================================================

(defn- route [env r] (fx/read! env (:signal r)))

(deftest router-signal
  (fx/each-world
   (fn [env]
     (testing "the initial route, from the default and from an explicit path"
       (is (= :home (:name (route env (router/router [["/" :home] ["/about" :about]])))))
       (let [r (router/router [["/" :home] ["/users/:id" :user]] {:path "/users/42?tab=posts"})]
         (is (= {:name :user :path "/users/42" :path-params {:id "42"} :query-params {:tab "posts"}}
                (route env r)))))
     (testing "navigate! and replace! by path, by name, with query params"
       (let [r (router/router [["/" :home] ["/about" :about] ["/users/:id" :user]])]
         (router/navigate! r "/about")
         (is (= :about (:name (route env r))))
         (router/navigate! r :user {:id "99"})
         (is (= {:id "99"} (:path-params (route env r))))
         (router/navigate! r :user {:id "1"} {:tab "posts"})
         (is (= {:tab "posts"} (:query-params (route env r))))
         (router/replace! r "/")
         (is (= :home (:name (route env r))))))
     (testing "href"
       (let [r (router/router [["/" :home] ["/users/:id" :user]])]
         (is (= "/users/123" (router/href r :user {:id "123"})))
         (is (= "/users/1?q=hi" (router/href r :user {:id "1"} {:q "hi"})))))
     (testing "the signal is in the router's world"
       (let [r (router/router [["/" :home]] {:world (:w env)})]
         (is (= :home (:name (route env r)))))))))

(deftest a-link-navigates-and-the-mount-commits-the-route
  (fx/each-world
   (fn [env]
     (let [r (router/router [["/" :home] ["/about" :about]])
           root (spin (let [{:keys [name]} (iv/get-new (track (:signal r)))]
                        (el/nav (link r :about {} {:class "nav"} "About")
                                (el/span (str name)))))
           {:keys [state] :as ctl} (fx/render! env root)
           d (:discharge (:mock env))
           a-el (get @(:elements (:mock env)) (:addr (first (:children (render/committed state)))))]
       (is (= [[:nav {} [:a {:class "nav" :href "/about"} "About"] [:span {} ":home"]]]
              (mock/dom d :container)))
       ((get (mock/attrs-of d a-el) :on-click) #?(:clj {} :cljs #js {:preventDefault (fn [])}))
       (fx/settle! env)
       (is (= [[:nav {} [:a {:class "nav" :href "/about"} "About"] [:span {} ":about"]]]
              (mock/dom d :container)))
       (fx/unmount! env ctl)
       (is (empty? (fx/leftovers env state)))))))
