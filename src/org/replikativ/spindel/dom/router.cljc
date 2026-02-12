(ns org.replikativ.spindel.dom.router
  "Signal-based router with browser History API integration.

   Three-layer architecture:
   1. Browser integration (CLJS only) - popstate/pushState
   2. Route matching (pure .cljc) - path <-> route data
   3. Router signal (Spindel reactive) - drives reactive DOM updates"
  (:require [clojure.string :as str]
            [org.replikativ.spindel.engine.core :as ec]
            #?(:clj [org.replikativ.spindel.signal :as sig])
            [org.replikativ.spindel.dom.elements :as el])
  #?(:cljs (:require-macros [org.replikativ.spindel.dom.router :refer [router link]])))

;; =============================================================================
;; Query String Helpers
;; =============================================================================

(defn- url-encode [s]
  #?(:clj  (java.net.URLEncoder/encode (str s) "UTF-8")
     :cljs (js/encodeURIComponent (str s))))

(defn- url-decode [s]
  #?(:clj  (java.net.URLDecoder/decode (str s) "UTF-8")
     :cljs (js/decodeURIComponent (str s))))

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

;; =============================================================================
;; Router Record
;; =============================================================================

(defrecord Router [routes signal])

;; =============================================================================
;; Router Creation
;; =============================================================================

#?(:clj
   (defmacro router
     "Create a Router with a signal holding current route data.
      Must be called within an execution context binding."
     ([route-defs]
      `(router ~route-defs {}))
     ([route-defs opts]
      `(let [compiled# (compile-routes ~route-defs)
             path# (or (:path ~opts) "/")
             initial# (match-route compiled# path#)
             sig# (sig/signal initial#)]
         (->Router compiled# sig#)))))

;; =============================================================================
;; Navigation
;; =============================================================================

(defn href
  "Generate a path string from route name, params, and optional query params.
   Pure function, no side effects.

   (href router :user {:id \"123\"})          -> \"/users/123\"
   (href router :user {:id \"1\"} {:q \"hi\"}) -> \"/users/1?q=hi\""
  ([router route-name params]
   (path-for (:routes router) route-name params))
  ([router route-name params query-params]
   (let [path (path-for (:routes router) route-name params)
         qs (build-query-string query-params)]
     (if qs (str path "?" qs) path))))

(defn- resolve-path
  "Resolve navigation arguments to a path string.
   Accepts either a path string or route-name + params + optional query-params."
  [router args]
  (let [[first-arg & rest-args] args]
    (if (keyword? first-arg)
      ;; Route name + params
      (let [[params query-params] rest-args
            path (path-for (:routes router) first-arg (or params {}))
            qs (build-query-string query-params)]
        (if qs (str path "?" qs) path))
      ;; Direct path string
      (str first-arg))))

(defn- navigate-impl!
  "Internal navigation implementation. Updates signal and optionally browser history."
  [router path-with-query history-fn]
  (let [route-data (match-route (:routes router) path-with-query)]
    #?(:cljs (when history-fn
               (history-fn (clj->js {}) "" path-with-query)))
    (reset! (:signal router) route-data)))

(defn navigate!
  "Navigate to a new route (pushState).

   By path:   (navigate! router \"/about\")
   By name:   (navigate! router :user {:id \"123\"})
   With query: (navigate! router :user {:id \"1\"} {:tab \"posts\"})"
  [router & args]
  (let [path (resolve-path router args)]
    (navigate-impl! router path
                    #?(:clj  nil
                       :cljs (fn [state title url]
                               (.pushState js/window.history state title url))))))

(defn replace!
  "Navigate to a new route (replaceState, no new history entry).

   Same argument forms as navigate!"
  [router & args]
  (let [path (resolve-path router args)]
    (navigate-impl! router path
                    #?(:clj  nil
                       :cljs (fn [state title url]
                               (.replaceState js/window.history state title url))))))

;; =============================================================================
;; Browser Integration (CLJS only)
;; =============================================================================

#?(:cljs
   (defn start!
     "Initialize browser routing. Reads current URL, sets signal, installs popstate listener.
      Returns a stop function that removes the listener.

      Optionally accepts an execution context that will be bound when handling
      popstate events (browser back/forward), ensuring reactive propagation works.

      (def stop-router! (router/start! my-router))
      (def stop-router! (router/start! my-router my-context))"
     ([router] (start! router nil))
     ([router ctx]
      (let [do-reset! (if ctx
                        (fn [route-data]
                          (binding [ec/*execution-context* ctx]
                            (reset! (:signal router) route-data)))
                        (fn [route-data]
                          (reset! (:signal router) route-data)))
            current-path (str js/window.location.pathname js/window.location.search)
            initial-route (match-route (:routes router) current-path)
            handler (fn [_event]
                      (let [path (str js/window.location.pathname js/window.location.search)
                            route-data (match-route (:routes router) path)]
                        (do-reset! route-data)))]
        ;; Set initial route from current URL
        (do-reset! initial-route)
        ;; Listen for back/forward navigation
        (.addEventListener js/window "popstate" handler)
        ;; Return stop function
        (fn stop! []
          (.removeEventListener js/window "popstate" handler))))))

;; =============================================================================
;; Link Component
;; =============================================================================

#?(:clj
   (defmacro link
     "Render an <a> element with click interception for client-side navigation.

      (link router :about {} \"About Page\")
      (link router :user {:id \"123\"} \"View User\")
      (link router :home {} {:class \"nav-link\"} \"Home\")"
     [router-expr route-name params & children]
     (let [;; If first child is a map literal, treat as extra attrs
           [extra-attrs children] (if (and (seq children)
                                           (map? (first children)))
                                    [(first children) (rest children)]
                                    [{} children])]
       `(let [r# ~router-expr
              path# (href r# ~route-name ~params)
              attrs# (merge ~extra-attrs
                            {:href path#
                             :on-click (fn [e#]
                                         #?(:cljs (.preventDefault e#))
                                         (navigate! r# path#))})]
          (el/a attrs# ~@children)))))
