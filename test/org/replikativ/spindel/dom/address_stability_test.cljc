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

(defn run-with-signal-change!
  "Run a spin that tracks a signal, collect results from two renders.
   Returns {:render-1 ... :render-2 ...} from the result-fn."
  [initial-value new-value render-fn]
  (let [test-ctx (ctx/create-execution-context)
        render-count (atom 0)
        results (atom {})]
    (try
      (binding [ec/*execution-context* test-ctx]
        (let [sig (sig/signal test-ctx initial-value)
              the-spin (spin
                         (let [data-iv (track sig)
                               data (iv/get-new data-iv)
                               rid (swap! render-count inc)]
                           (swap! results assoc rid (render-fn data))
                           (render-fn data)))]
          (the-spin
            (fn [_] (when (= 1 @render-count)
                      (reset! sig new-value)))
            (fn [err] (throw (ex-info "Spin error" {:error err}))))
          ;; Wait for drain to process signal change
          #?(:clj (Thread/sleep 1000)
             :cljs nil)))
      (finally
        (ctx/stop-context! test-ctx)))
    @results))

;; =============================================================================
;; Tests
;; =============================================================================

(deftest test-root-address-stable
  (testing "Root element address is identical across signal-change re-renders"
    (let [results (run-with-signal-change!
                    nil "data"
                    (fn [data]
                      (let [vdom (el/div {:class "root"}
                                  (el/span {} (str data)))]
                        {:addr (:addr vdom)
                         :parent (addr/get-parent-addr)
                         :slot (addr/get-current-slot)})))]
      (is (= 2 (count results)) "Should have two renders")
      (is (= (:addr (get results 1)) (:addr (get results 2)))
          "Root address must be stable across re-renders")
      (is (nil? (:parent (get results 1))) "Parent should be nil on first render")
      (is (nil? (:parent (get results 2))) "Parent should be nil on re-render"))))

(deftest test-nested-addresses-stable
  (testing "All shared element addresses are stable across re-renders"
    (let [results (run-with-signal-change!
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
                        (collect-addresses vdom))))]
      (is (= 2 (count results)))
      (let [a1 (get results 1)
            a2 (get results 2)
            shared (set/intersection a1 a2)]
        ;; app-div, sidebar-aside, sidebar-span, content-div = 4 shared
        (is (>= (count shared) 4)
            (str "Expected at least 4 shared addresses, got " (count shared)))))))

(deftest test-dom-context-nil-at-track-resume
  (testing "DOM context bindings are nil when spin resumes from track"
    (let [results (run-with-signal-change!
                    :v1 :v2
                    (fn [val]
                      {:parent (addr/get-parent-addr)
                       :slot (addr/get-current-slot)
                       :val val}))]
      (is (= 2 (count results)))
      (doseq [[rid {:keys [parent slot val]}] results]
        (is (nil? parent)
            (str "parent-addr should be nil at track point (render " rid ", val=" val ")"))
        (is (nil? slot)
            (str "current-slot should be nil at track point (render " rid ", val=" val ")"))))))

(deftest test-nested-spin-address-stability
  (testing "Addresses stable when inner spin is awaited during re-render"
    (let [test-ctx (ctx/create-execution-context)
          render-count (atom 0)
          addresses (atom {})]
      (try
        (binding [ec/*execution-context* test-ctx]
          (let [sig (sig/signal test-ctx nil)
                the-spin (spin
                           (let [data-iv (track sig)
                                 data (iv/get-new data-iv)
                                 rid (swap! render-count inc)
                                 inner (spin
                                         (el/div {:class "wrapper"}
                                           (el/nav {} (el/span {} "Menu"))
                                           (el/main {}
                                             (el/p {} (or data "empty")))))
                                 vdom (await inner)]
                             (swap! addresses assoc rid (collect-addresses vdom))
                             vdom))]
            (the-spin
              (fn [_] (when (= 1 @render-count)
                        (reset! sig "content")))
              (fn [err] (throw (ex-info "Error" {:error err}))))
            #?(:clj (Thread/sleep 2000) :cljs nil)))
        (finally
          (ctx/stop-context! test-ctx)))
      (is (= 2 (count @addresses)) "Should have two renders")
      (when (= 2 (count @addresses))
        (let [a1 (get @addresses 1)
              a2 (get @addresses 2)
              shared (set/intersection a1 a2)]
          ;; wrapper, nav, nav-span, main = 4 shared
          (is (>= (count shared) 4)
              (str "Expected at least 4 shared addresses in nested spin, got "
                   (count shared))))))))
