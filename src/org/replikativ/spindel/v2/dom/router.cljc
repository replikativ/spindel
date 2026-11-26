(ns org.replikativ.spindel.v2.dom.router
  "Signal-based router on engine v2, with browser History API integration.

   Three layers:
   1. Route matching (pure): path <-> route data.
   2. The router: compiled routes and a signal of the current route data,
      in the router's world; navigation writes the signal.
   3. Browser integration (CLJS): popstate and pushState/replaceState."
  (:require [clojure.string :as str]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.dom.elements :as el])
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.dom.router :refer [link]])))

;; =============================================================================
;; Query String Helpers
;; =============================================================================

(defn- url-encode [s]
  #?(:clj  (java.net.URLEncoder/encode (str s) "UTF-8")
     :cljs (js/encodeURIComponent (str s))))

(defn- url-decode [s]
  ;; application/x-www-form-urlencoded: '+' decodes to space.
  ;; JVM's URLDecoder handles this; JS decodeURIComponent does not, so we
  ;; preprocess for parity.
  #?(:clj  (java.net.URLDecoder/decode (str s) "UTF-8")
     :cljs (js/decodeURIComponent (str/replace (str s) "+" " "))))

(defn parse-query-string
  "Parse query string into a map of keyword keys to string values.
   \"foo=bar&baz=qux\" -> {:foo \"bar\" :baz \"qux\"}
   Empty or nil input -> {}"
  [qs]
  (if (or (nil? qs) (str/blank? qs))
    {}
    (->> (str/split qs #"&")
         (keep (fn [pair]
                 (let [parts (str/split pair #"=" 2)]
                   (when (and (first parts) (not (str/blank? (first parts))))
                     [(keyword (url-decode (first parts)))
                      (if (second parts) (url-decode (second parts)) "")]))))
         (into {}))))

(defn build-query-string
  "Build query string from a map. {:foo \"bar\"} -> \"foo=bar\"
   Empty or nil map -> nil"
  [params]
  (when (seq params)
    (->> params
         (map (fn [[k v]] (str (url-encode (name k)) "=" (url-encode (str v)))))
         (str/join "&"))))

;; =============================================================================
;; Route Compilation
;; =============================================================================

(defn- parse-segment
  "Parse a single path segment.
   \"users\" -> {:type :literal, :value \"users\"}
   \":id\"  -> {:type :param, :name :id}
   \"*rest\" -> {:type :wildcard, :name :rest}"
  [s]
  (cond
    (str/starts-with? s "*") {:type :wildcard :name (keyword (subs s 1))}
    (str/starts-with? s ":") {:type :param :name (keyword (subs s 1))}
    :else                    {:type :literal :value s}))

(defn compile-routes
  "Compile route definitions into internal representation.
   Parses pattern strings, classifying segments as literal, param, or wildcard."
  [route-defs]
  (mapv (fn [[pattern name-kw & _extra]]
          (let [path (if (= pattern "/") "" pattern)
                raw-segments (remove str/blank? (str/split path #"/"))
                segments (mapv parse-segment raw-segments)
                param-names (into [] (comp (filter #(= :param (:type %)))
                                           (map :name))
                                  segments)
                wildcard? (some #(= :wildcard (:type %)) segments)]
            {:pattern pattern
             :name name-kw
             :segments segments
             :param-names param-names
             :wildcard? (boolean wildcard?)}))
        route-defs))

;; =============================================================================
;; Route Matching
;; =============================================================================

(defn- match-segments
  "Try to match path parts against compiled route segments.
   Returns path-params map on success, nil on failure."
  [segments parts]
  (loop [segs segments
         pts parts
         params {}]
    (cond
      ;; All segments consumed - match if no leftover parts
      (empty? segs)
      (when (empty? pts) params)

      ;; Wildcard segment - consumes all remaining parts
      (= :wildcard (:type (first segs)))
      (assoc params (:name (first segs)) (str/join "/" pts))

      ;; No more parts but segments remain - no match
      (empty? pts) nil

      ;; Literal segment - must match exactly
      (= :literal (:type (first segs)))
      (when (= (:value (first segs)) (first pts))
        (recur (rest segs) (rest pts) params))

      ;; Param segment - capture value
      (= :param (:type (first segs)))
      (recur (rest segs) (rest pts)
             (assoc params (:name (first segs)) (first pts))))))

(defn match-route
  "Match a path string against compiled routes. First match wins.
   Returns route data map:
   {:name :user :path \"/users/123\" :path-params {:id \"123\"} :query-params {:tab \"posts\"}}"
  [compiled-routes path-with-query]
  (let [[path query-str] (str/split (or path-with-query "/") #"\?" 2)
        path (if (str/blank? path) "/" path)
        parts (remove str/blank? (str/split path #"/"))
        query-params (parse-query-string query-str)]
    (or (some (fn [route]
                (when-let [path-params (match-segments (:segments route) parts)]
                  {:name (:name route)
                   :path path
                   :path-params path-params
                   :query-params query-params}))
              compiled-routes)
        {:name nil
         :path path
         :path-params {}
         :query-params query-params})))

;; =============================================================================
;; Reverse Routing
;; =============================================================================

(defn path-for
  "Generate a path from route name and params (reverse routing).
   (path-for compiled :user {:id \"123\"}) -> \"/users/123\""
  [compiled-routes route-name params]
  (if-let [route (first (filter #(= route-name (:name %)) compiled-routes))]
    (let [path (->> (:segments route)
                    (map (fn [seg]
                           (case (:type seg)
                             :literal (:value seg)
                             :param   (let [v (get params (:name seg))]
                                        (when (nil? v)
                                          (throw (ex-info (str "Missing param " (:name seg)
                                                               " for route " route-name)
                                                          {:route route-name
                                                           :param (:name seg)
                                                           :params params})))
                                        (str v))
                             :wildcard (or (get params (:name seg)) ""))))
                    (str/join "/"))]
      (str "/" path))
    (throw (ex-info (str "Route not found: " route-name)
                    {:route-name route-name}))))

(defrecord Router [routes signal])

(defn router
  "A Router: compiled `route-defs` and a signal of the route data, in the
   world `(:world opts)` or `(v2/current-world)`, starting at `(:path opts)`
   (default \"/\")."
  ([route-defs] (router route-defs {}))
  ([route-defs {:keys [path world]}]
   (let [compiled (compile-routes route-defs)
         w (or world (v2/current-world))]
     (->Router compiled (v2/signal w (match-route compiled (or path "/")))))))

;; =============================================================================
;; Navigation
;; =============================================================================

(defn href
  "The path of route `route-name` with `params` and optional `query-params`.
   (href router :user {:id \"123\"}) -> \"/users/123\""
  ([router route-name params]
   (path-for (:routes router) route-name params))
  ([router route-name params query-params]
   (let [path (path-for (:routes router) route-name params)
         qs (build-query-string query-params)]
     (if qs (str path "?" qs) path))))

(defn- resolve-path
  "A path string from navigation arguments: a path, or a route name with
   params and optional query params."
  [router [first-arg & rest-args]]
  (if (keyword? first-arg)
    (let [[params query-params] rest-args]
      (href router first-arg (or params {}) query-params))
    (str first-arg)))

(defn- navigate-impl!
  [router path-with-query history-fn]
  (let [route-data (match-route (:routes router) path-with-query)]
    ;; no history outside a browser (Node, SSR): the signal alone moves
    #?(:cljs (when (and history-fn (exists? js/window) (.-history js/window))
               (history-fn #js {} "" path-with-query))
       :clj (do history-fn nil))
    (reset! (:signal router) route-data)))

(defn navigate!
  "Navigates (pushState in the browser).
   By path:    (navigate! router \"/about\")
   By name:    (navigate! router :user {:id \"123\"})
   With query: (navigate! router :user {:id \"1\"} {:tab \"posts\"})"
  [router & args]
  (navigate-impl! router (resolve-path router args)
                  #?(:clj nil
                     :cljs (fn [state title url] (.pushState js/window.history state title url)))))

(defn replace!
  "Navigates without a new history entry (replaceState). Same arguments as
   navigate!."
  [router & args]
  (navigate-impl! router (resolve-path router args)
                  #?(:clj nil
                     :cljs (fn [state title url] (.replaceState js/window.history state title url)))))

;; =============================================================================
;; Browser integration (CLJS)
;; =============================================================================

#?(:cljs
   (defn start!
     "Sets the route from the current URL and follows back/forward
      navigation (popstate). Returns a fn that stops following."
     [router]
     (let [route! (fn []
                    (reset! (:signal router)
                            (match-route (:routes router)
                                         (str js/window.location.pathname js/window.location.search))))
           handler (fn [_] (route!))]
       (route!)
       (.addEventListener js/window "popstate" handler)
       (fn stop! [] (.removeEventListener js/window "popstate" handler)))))

;; =============================================================================
;; Link
;; =============================================================================

(defn ^:no-doc prevent-default!
  "Calls the event's preventDefault where there is one."
  [e]
  #?(:cljs (when (and e (.-preventDefault e)) (.preventDefault e))
     :clj (do e nil)))

#?(:clj
   (defmacro link
     "An <a> to route `route-name` whose click navigates on the client.
      A literal map as the first child is merged into the attrs.

      (link router :about {} \"About\")
      (link router :user {:id \"123\"} {:class \"nav\"} \"View User\")"
     [router-expr route-name params & children]
     (let [[extra children] (if (and (seq children) (map? (first children)))
                              [(first children) (rest children)]
                              [{} children])
           r (gensym "router")
           path (gensym "path")
           e (gensym "e")
           attrs (merge extra {:href path
                               :on-click `(fn [~e] (prevent-default! ~e) (navigate! ~r ~path))})]
       `(let [~r ~router-expr
              ~path (href ~r ~route-name ~params)]
          ~(with-meta `(el/a ~attrs ~@children) (meta &form))))))
