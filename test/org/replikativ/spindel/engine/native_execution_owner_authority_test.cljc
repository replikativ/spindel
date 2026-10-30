(ns org.replikativ.spindel.engine.native-execution-owner-authority-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]))

(defn- ignore-result [_])

(defn- parked-owner [rt]
  (binding [ec/*execution-context* rt]
    (let [captured (atom nil)
          pending (sync/deferred)
          target (spin-core/make-spin
                  (fn [succeed fail]
                    (reset! captured (lifetime/current-scope rt))
                    (pending succeed fail)
                    spin-core/incomplete)
                  :scope-owner-authority)]
      (target ignore-result ignore-result)
      (when-not (= :parked (get-in (owned/snapshot rt) [:runs [:scope-owner-authority 1] :status]))
        (throw (ex-info "Authority fixture did not park its named Run" {})))
      {:owner @captured :target target :pending pending})))

(deftest owner-authority-is-distinct-between-equal-coordinate-runtimes
  (let [left (owned/runtime {:audit? true :cps-exit? true})
        right (owned/runtime {:audit? true :cps-exit? true})]
    (try
      (let [left-fixture (parked-owner left)
            right-fixture (parked-owner right)
            left-owner (:owner left-fixture)
            right-owner (:owner right-fixture)
            left-scope (lifetime/open-scope! left :explicit left-owner)
            before (owned/snapshot right)]
        (is (= (:world left) (:world right)))
        (is (= (set (keys (:runs (owned/snapshot left))))
               (set (keys (:runs before)))) "Both worlds deliberately have the same Run coordinates")
        (is (some? left-owner))
        (is (some? right-owner))
        (is (identical? left-owner (lifetime/bindable-scope left left-owner)))
        (is (identical? right-owner (lifetime/bindable-scope right right-owner)))
        (doseq [foreign [left-owner left-scope (lifetime/root-scope left)]]
          (is (thrown? #?(:clj Exception :cljs js/Error) (lifetime/bindable-scope right foreign)))
          (is (thrown? #?(:clj Exception :cljs js/Error) (lifetime/open-scope! right :explicit foreign)))
          (is (= before (owned/snapshot right))))
        (is (thrown? #?(:clj Exception :cljs js/Error)
                     (lifetime/bindable-scope right [:run owned/w :scope-owner-authority 1])))
        (is (= before (owned/snapshot right)))
        (lifetime/close-scope! left left-scope))
      (finally
        (context/release-context! left)
        (context/release-context! right)))))
