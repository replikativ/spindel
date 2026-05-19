(ns org.replikativ.spindel.dom.address-stability-test
  "Tests that DOM addresses are stable across signal-change re-renders.

   The address system computes hash(source-loc, parent-addr, slot-index)
   for each element. When a spin re-executes from a track continuation,
   the DOM context bindings (parent-addr, slot) must be clean so that
   element macros compute the same addresses as the initial render."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.addressing :as addr]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.test-helpers :refer [async]]
            [clojure.set :as set])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.dom.elements :as el])))

#?(:clj (require '[org.replikativ.spindel.spin.cps :refer [spin]]))

;; =============================================================================
;; Helpers
;; =============================================================================

(defn collect-addresses
  "Walk a vnode tree and collect all addresses into a set."
  [vnode]
  (when vnode
    (let [addr (:addr vnode)
          children (when-let [ch (:children vnode)]
                     (try @ch (catch #?(:clj Exception :cljs :default) _ ch)))]
      (into (if addr #{addr} #{})
            (mapcat collect-addresses)
            (when (sequential? children) children)))))

(defn- await-renders
  "Poll the render-count atom until it reaches `expected` (or timeout) and
  call `on-ready`. Cross-platform: blocks via Thread/sleep on JVM, uses
  setTimeout on CLJS."
  [render-count expected timeout-ms on-ready]
  #?(:clj
     (let [deadline (+ (System/currentTimeMillis) timeout-ms)]
       (loop []
         (cond
           (= @render-count expected) (on-ready)
           (>= (System/currentTimeMillis) deadline) (on-ready)
           :else (do (Thread/sleep 20) (recur)))))
     :cljs
     (let [deadline (+ (.now js/Date) timeout-ms)
           tick (fn tick []
                  (cond
                    (= @render-count expected) (on-ready)
                    (>= (.now js/Date) deadline) (on-ready)
                    :else (js/setTimeout tick 20)))]
       (tick))))

(defn with-signal-change
  "Run a spin that tracks a signal, collect render-1 then trigger
  `new-value` to get render-2. Calls `(on-done results)` with a
  {render-id -> render-fn-result} map.

  This helper is async on CLJS (the second render lands via setTimeout)
  and synchronous on JVM (we Thread/sleep the calling thread)."
  [initial-value new-value render-fn on-done]
  (let [test-ctx (ctx/create-execution-context)
        render-count (atom 0)
        results (atom {})]
    (binding [ec/*execution-context* test-ctx]
      (let [sig (sig/signal test-ctx initial-value)
            the-spin (spin
                      (let [data-iv (track sig)
                            data (iv/get-new data-iv)
                            rendered (render-fn data)
                             ;; CRITICAL: write the result into `results` BEFORE
                             ;; bumping render-count. await-renders polls render-count
                             ;; and fires on-done the moment it sees the expected
                             ;; value — if we increment first and then assoc, the
                             ;; poller can wedge between those two ops and read a
                             ;; results map that's missing this render's entry.
                            rid (inc @render-count)
                            _ (swap! results assoc rid rendered)
                            _ (swap! render-count inc)]
                        rendered))]
        (the-spin
         (fn [_] (when (= 1 @render-count)
                   (reset! sig new-value)))
         (fn [err] (throw (ex-info "Spin error" {:error err}))))
        (await-renders render-count 2 2000
                       (fn []
                         (try (on-done @results)
                              (finally (ctx/stop-context! test-ctx)))))))))

;; =============================================================================
;; Tests
;; =============================================================================

(deftest test-root-address-stable
  (testing "Root element address is identical across signal-change re-renders"
    (async done
           (with-signal-change
             nil "data"
             (fn [data]
               (let [vdom (el/div {:class "root"}
                                  (el/span {} (str data)))]
                 {:addr (:addr vdom)
                  :parent (addr/get-parent-addr)
                  :slot (addr/get-current-slot)}))
             (fn [results]
               (is (= 2 (count results)) "Should have two renders")
               (is (= (:addr (get results 1)) (:addr (get results 2)))
                   "Root address must be stable across re-renders")
               (is (nil? (:parent (get results 1))) "Parent should be nil on first render")
               (is (nil? (:parent (get results 2))) "Parent should be nil on re-render")
               (done))))))

(deftest test-nested-addresses-stable
  (testing "All shared element addresses are stable across re-renders"
    (async done
           (with-signal-change
             nil "loaded"
             (fn [data]
               (let [vdom (el/div {:class "app"}
                                  (el/aside {:class "sidebar"}
                                            (el/span {} "Nav"))
                                  (el/div {:class "content"}
                                          (if data
                                            (el/div {:class "loaded"}
                                                    (el/p {} (str data)))
                                            (el/div {:class "loading"}
                                                    (el/p {} "...")))))]
                 (collect-addresses vdom)))
             (fn [results]
               (is (= 2 (count results)))
               (let [a1 (get results 1)
                     a2 (get results 2)
                     shared (set/intersection a1 a2)]
            ;; app-div, sidebar-aside, sidebar-span, content-div = 4 shared
                 (is (>= (count shared) 4)
                     (str "Expected at least 4 shared addresses, got " (count shared))))
               (done))))))

(deftest test-dom-context-nil-at-track-resume
  (testing "DOM context bindings are nil when spin resumes from track"
    (async done
           (with-signal-change
             :v1 :v2
             (fn [val]
               {:parent (addr/get-parent-addr)
                :slot (addr/get-current-slot)
                :val val})
             (fn [results]
               (is (= 2 (count results)))
               (doseq [[rid {:keys [parent slot val]}] results]
                 (is (nil? parent)
                     (str "parent-addr should be nil at track point (render " rid ", val=" val ")"))
                 (is (nil? slot)
                     (str "current-slot should be nil at track point (render " rid ", val=" val ")")))
               (done))))))

(deftest test-nested-spin-address-stability
  (testing "Addresses stable when inner spin is awaited during re-render"
    (async done
           (let [test-ctx (ctx/create-execution-context)
                 render-count (atom 0)
                 addresses (atom {})]
             (binding [ec/*execution-context* test-ctx]
               (let [sig (sig/signal test-ctx nil)
                     the-spin (spin
                               (let [data-iv (track sig)
                                     data (iv/get-new data-iv)
                                     inner (spin
                                            (el/div {:class "wrapper"}
                                                    (el/nav {} (el/span {} "Menu"))
                                                    (el/main {}
                                                             (el/p {} (or data "empty")))))
                                     vdom (await inner)
                                 ;; Same ordering rule as with-signal-change:
                                 ;; populate `addresses` BEFORE bumping
                                 ;; render-count, otherwise the poller can
                                 ;; observe count=2 and read a stale map.
                                     rid (inc @render-count)
                                     _ (swap! addresses assoc rid (collect-addresses vdom))
                                     _ (swap! render-count inc)]
                                 vdom))]
                 (the-spin
                  (fn [_] (when (= 1 @render-count)
                            (reset! sig "content")))
                  (fn [err] (throw (ex-info "Error" {:error err}))))
                 (await-renders render-count 2 2000
                                (fn []
                                  (try
                                    (is (= 2 (count @addresses)) "Should have two renders")
                                    (when (= 2 (count @addresses))
                                      (let [a1 (get @addresses 1)
                                            a2 (get @addresses 2)
                                            shared (set/intersection a1 a2)]
                      ;; wrapper, nav, nav-span, main = 4 shared
                                        (is (>= (count shared) 4)
                                            (str "Expected at least 4 shared addresses in nested spin, got "
                                                 (count shared)))))
                                    (finally
                                      (ctx/stop-context! test-ctx)
                                      (done)))))))))))
