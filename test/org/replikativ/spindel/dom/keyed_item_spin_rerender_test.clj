(ns org.replikativ.spindel.dom.keyed-item-spin-rerender-test
  "Regression: an `ifor-each` item whose `render-fn` returns a *spin* must
  keep its keyed element address stable when the PARENT re-renders — e.g. a
  sibling signal change escalates a re-run of the for-each's parent spin.

  This is the property-box DOM-duplication bug. `render-column` is a keyed
  `ifor-each` item-spin; on a parent re-render its column `el/div` addressed
  structurally (`:dom/parent-addr` nil) instead of keyed, drifting the
  address -> `reconcilable?` fails -> destroy+recreate -> shared keyed
  caches evicted -> duplicated DOM.

  The item-spin's keyed DOM scope must be intrinsic to the spin and
  re-established on every body run, not snapshotted from a transient
  dynamic-scope extent that only covers construction."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(defn- class-addrs
  "Walk a vnode / KeyedFragment tree -> {class-string -> :addr}."
  [node]
  (cond
    (nil? node) {}
    (frag/keyed-fragment? node)
    (apply merge (map class-addrs (frag/fragment-items node)))
    (and (map? node) (:tag node))
    (let [attrs    (let [a (:attrs node)] (if (d/deltaable? a) @a a))
          cls      (:class attrs)
          children (let [c (:children node)] (if (d/deltaable? c) @c c))
          kids     (apply merge (map class-addrs
                                     (when (sequential? children) children)))]
      (merge (if cls {cls (:addr node)} {}) kids))
    :else {}))

(defn- await-count [a expected timeout-ms]
  (let [deadline (+ (System/currentTimeMillis) timeout-ms)]
    (loop []
      (cond
        (>= @a expected)                          true
        (>= (System/currentTimeMillis) deadline)  false
        :else (do (Thread/sleep 20) (recur))))))

(deftest test-keyed-item-spin-address-stable-across-parent-rerender
  (testing "keyed ifor-each item-spin keeps its keyed element address when the parent re-renders"
    (let [test-ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* test-ctx]
        (let [trigger       (sig/signal test-ctx 0)
              columns       [{:id "col-1" :title "Column 1"}
                             {:id "col-2" :title "Column 2"}]
              render-column (fn [col]
                              (spin
                               (el/div {:key   (:id col)
                                        :class (str "column-" (:id col))}
                                       (el/span {} (:title col)))))
              results       (atom {})
              render-count  (atom 0)
              parent        (spin
                             (let [t-iv (track trigger)
                                   _t   (iv/get-new t-iv)
                                   fr   (await (foreach/for-each*
                                                {:file "kis" :line 1 :column 1}
                                                :id render-column columns))
                                   vdom (el/div {:class "columns-container"} fr)
                                   rid  (inc @render-count)
                                   _    (swap! results assoc rid (class-addrs vdom))
                                   _    (swap! render-count inc)]
                               vdom))]
          (parent
           (fn [_] (when (= 1 @render-count) (reset! trigger 1)))
           (fn [err] (throw (ex-info "parent spin failed" {:err err}))))
          (is (await-count render-count 2 3000) "two renders completed")
          (let [r1 (get @results 1)
                r2 (get @results 2)]
            (is (some? r1) "render 1 collected")
            (is (some? r2) "render 2 collected")
            (doseq [cls ["columns-container" "column-col-1" "column-col-2"]]
              (is (= (get r1 cls) (get r2 cls))
                  (str cls " address must be stable across parent re-render: "
                       "render1=" (get r1 cls) " render2=" (get r2 cls)))))
          (ctx/stop-context! test-ctx))))))

(deftest test-keyed-item-spin-address-stable-across-escalated-rerender
  (testing "keyed ifor-each item-spin keeps its keyed address when a signal
            tracked DEEP inside the item escalates a re-run of the for-each's
            parent (the property-box DOM-duplication path)"
    (let [test-ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* test-ctx]
        (let [trigger       (sig/signal test-ctx 0)
              columns       [{:id "col-1" :title "Column 1"}
                             {:id "col-2" :title "Column 2"}]
              ;; property-box analog: a spin nested inside the column that
              ;; tracks `trigger`. Toggling `trigger` escalates a re-run up
              ;; to columns-container, which re-runs for-each*.
              render-inner  (fn [col]
                              (spin
                               (let [iv-t (track trigger)
                                     v    (iv/get-new iv-t)]
                                 (el/div {:class (str "inner-" (:id col))}
                                         (str (:title col) "-" v)))))
              render-column (fn [col]
                              (spin
                               (let [inner (await (render-inner col))]
                                 (el/div {:key   (:id col)
                                          :class (str "column-" (:id col))}
                                         inner))))
              results       (atom {})
              render-count  (atom 0)
              columns-container
              (spin
               (let [fr   (await (foreach/for-each*
                                  {:file "kis" :line 2 :column 1}
                                  :id render-column columns))
                     vdom (el/div {:class "columns-container"} fr)
                     rid  (inc @render-count)
                     _    (swap! results assoc rid (class-addrs vdom))
                     _    (swap! render-count inc)]
                 vdom))]
          (columns-container
           (fn [_] (when (= 1 @render-count) (reset! trigger 1)))
           (fn [err] (throw (ex-info "columns-container failed" {:err err}))))
          (is (await-count render-count 2 3000) "two renders completed")
          (let [r1 (get @results 1)
                r2 (get @results 2)]
            (is (some? r1) "render 1 collected")
            (is (some? r2) "render 2 collected")
            (doseq [cls ["columns-container"
                         "column-col-1" "column-col-2"
                         "inner-col-1" "inner-col-2"]]
              (is (= (get r1 cls) (get r2 cls))
                  (str cls " address must be stable across escalated re-render: "
                       "render1=" (get r1 cls) " render2=" (get r2 cls)))))
          (ctx/stop-context! test-ctx))))))
