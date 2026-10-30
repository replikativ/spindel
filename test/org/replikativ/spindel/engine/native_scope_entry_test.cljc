(ns org.replikativ.spindel.engine.native-scope-entry-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [is.simm.partial-cps.runtime :as cps-runtime]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.spin.core :as spin-core]))

(deftest scope-restoration-preserves-exact-binding-data-and-map-shape
  (let [bindings (with-meta {:scope :same} {:origin :current})
        current {:bindings bindings :other :kept}
        captured (with-meta {:scope :same} {:origin :captured})
        restored (ec/restore-context-scope captured current)]
    (is (identical? current (ec/restore-context-scope bindings current)))
    (is (identical? captured (:bindings restored)))
    (is (= :captured (:origin (meta (:bindings restored)))))
    (is (= :kept (:other restored)))
    (is (contains? (ec/restore-context-scope nil {}) :bindings))
    (is (= {:bindings nil} (ec/restore-context-scope nil {})))
    (is (nil? (ec/restore-context-scope bindings nil)))))

(defn- capture-probe [] :probe)
(defn- restore-probe [value] value)
(defn- bind-probe [_ f] (f))

(deftest native-entry-preserves-unrelated-descriptors-and-isolates-dynamic-set
  (let [rt (owned/runtime {:audit? true :cps-exit? true :bindings {}})
        caller (assoc rt :bindings {:scope :caller})
        descriptors {'scope-entry/probe [capture-probe restore-probe bind-probe]}
        values (atom []) errors (atom [])]
    (binding [ec/*execution-context* caller
              ec/*spin-id* :outside
              ec/*run-gen* [:outside 9]
              ec/*lifetime-run* 9
              ec/*owner-scope* [:outside-owner]
              cps-runtime/*scope-frame* descriptors]
      (let [task (spin-core/make-spin
                  (fn [succeed _fail]
                    (let [before [(contains? cps-runtime/*scope-frame* 'scope-entry/probe)
                                  ec/*spin-id* ec/*run-gen* ec/*lifetime-run* ec/*owner-scope*]]
                      (set! ec/*execution-context* (assoc rt :bindings {:scope :changed}))
                      (set! ec/*spin-id* :changed)
                      (set! ec/*run-gen* [:changed 42])
                      (set! ec/*lifetime-run* 42)
                      (set! ec/*owner-scope* [:changed-owner])
                      (set! cps-runtime/*scope-frame* {})
                      (succeed [before (get-in (ec/current-execution-context) [:bindings :scope])
                                ec/*spin-id* ec/*run-gen* ec/*lifetime-run* ec/*owner-scope*])))
                  :scope-entry)]
        (task #(swap! values conj %) #(swap! errors conj %)))
      (is (identical? caller ec/*execution-context*))
      (is (= :outside ec/*spin-id*))
      (is (= [:outside 9] ec/*run-gen*))
      (is (= 9 ec/*lifetime-run*))
      (is (= [:outside-owner] ec/*owner-scope*))
      (is (identical? descriptors cps-runtime/*scope-frame*)))
    (is (empty? @errors))
    (is (= [[[true :scope-entry [:scope-entry 1] 1 [:run owned/w :scope-entry 1]]
             :changed :changed [:changed 42] 42 [:changed-owner]]]
           @values))
    (verify-boundaries! rt)))
