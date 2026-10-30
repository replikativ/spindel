(ns org.replikativ.spindel.engine.native-execution-scope-cleanup-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]))

(deftest closing-a-scope-retains-its-shared-cell-through-child-finally-return
  (let [rt (context/create-execution-context {:engine :owned})
        scope (lifetime/open-scope! rt :explicit)
        trace (atom []) values (atom []) errors (atom [])]
    (try
      (binding [ec/*execution-context* rt]
        (let [pending (sync/deferred)
              ack (sync/deferred)
              target (lifetime/with-owner scope
                       (let [cell (ratom/atom :scope-owned)]
                         (spin
                          (try
                            (await pending)
                            (finally
                              (await-finalization ack)
                              (swap! trace conj [@cell (rtp/execution-owner-joined? rt scope)]))))))]
          (lifetime/with-owner scope
            (target #(swap! values conj %) #(swap! errors conj %)))
          (is (nil? (lifetime/close-scope! rt scope)))
          (is (= 1 (count @errors)) "Logical cancellation is reported before asynchronous cleanup")
          (is (empty? @values))
          (is (empty? @trace))
          (is (false? (rtp/execution-owner-joined? rt scope)))
          (is (thrown? #?(:clj Exception :cljs js/Error) (lifetime/bindable-scope rt scope)))
          (ack nil)
          (is (= [[:scope-owned false]] @trace)
              "A scope-owned cell survives cleanup, and a frame cannot certify its own physical return")
          (is (true? (rtp/execution-owner-joined? rt scope)))
          (is (= :live (:status (owned/snapshot rt))))))
      (finally (context/release-context! rt)))))
