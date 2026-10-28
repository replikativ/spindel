(ns org.replikativ.spindel.engine.lifetime-owner-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.engine.core :as ec]
            #?(:clj [org.replikativ.spindel.engine.context :as ctx])
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

(defn- finish-async! [done]
  #?(:clj (done)
     :cljs (js/setTimeout done 0)))

(deftest owned-creation-and-invocation
  (async done
         (with-ctx [ctx]
           (let [scope (lifetime/open-scope! ctx :supervisor)
                 root (lifetime/root-scope ctx)]
             (binding [ec/*owner-scope* scope]
               (let [parent (spin
                             (let [source (sig/signal 1)
                                   cell (ratom/create-atom 2)
                                   child (spin (iv/get-new (track source)))]
                               (await child)
                               {:source (:id source)
                                :cell (ratom/atom-id cell)
                                :child (spin-core/spin-id child)}))
                     parent-id (spin-core/spin-id parent)]
                 (run-spin! parent
                            (fn [{:keys [source cell child]}]
                              (let [parent-node (rtp/get-state ctx [:nodes parent-id])
                                    parent-run (lifetime/body-run-id ctx parent-id)
                                    child-node (rtp/get-state ctx [:nodes child])]
                                (is (= root (get-in (rtp/get-state ctx [:lifetime/scopes])
                                                    [scope :parent])))
                                (is (= scope (:lifetime/owner parent-node)))
                                (is (= scope (:lifetime/run-owner parent-node)))
                                (is (= parent-run (:lifetime/owner child-node)))
                                (is (= parent-run (:lifetime/creator child-node)))
                                (is (= parent-run (:lifetime/run-owner child-node)))
                                (is (= parent-run (rtp/get-state ctx [:nodes source :lifetime/owner])))
                                (is (= parent-run (rtp/get-state ctx [:atoms cell :lifetime/owner])))
                                (finish-async! done)))
                            (fn [error]
                              (is false (str error))
                              (finish-async! done)))))))))

(deftest lexical-creation-uses-creating-run
  (async done
         (with-ctx [ctx]
           (binding [ec/*owner-scope* nil]
             (let [parent (spin
                           (let [source (sig/signal 1)
                                 child (spin (iv/get-new (track source)))]
                             (await child)
                             {:source (:id source) :child (spin-core/spin-id child)}))
                   parent-id (spin-core/spin-id parent)]
               (run-spin! parent
                          (fn [{:keys [source child]}]
                            (let [parent-run (lifetime/body-run-id ctx parent-id)
                                  child-node (rtp/get-state ctx [:nodes child])]
                              (is (= parent-run (:lifetime/owner child-node)))
                              (is (= parent-run (:lifetime/creator child-node)))
                              (is (= parent-run (:lifetime/run-owner child-node)))
                              (is (= parent-run (rtp/get-state ctx [:nodes source :lifetime/owner])))
                              (done)))
                          (fn [error]
                            (is false (str error))
                            (done))))))))

#?(:clj
   (deftest direct-caller-joins-reserved-execution
     (with-ctx [ctx]
       (let [runs (atom 0)
             delivered (atom [])
             s (spin (do (swap! runs inc) 7))
             id (spin-core/spin-id s)
             resolve #(swap! delivered conj %)
             reject #(throw %)]
         (is (true? (simple/try-claim-execution! ctx id)))
         (s resolve reject)
         (is (empty? @delivered))
         (is (zero? @runs))
         (binding [simple/*execution-claim* id]
           (s resolve reject))
         (is (= 1 @runs))
         (is (= [7 7] @delivered))))))

#?(:clj
   (deftest keyed-signal-is-adopted-by-successor-run
     (with-ctx [ctx]
       (let [reached (promise)
             created (atom [])
             source (sig/signal 1)
             s (spin (let [value (iv/get-new (track source))
                           owned (sig/signal :owned)]
                       (swap! created conj (:id owned))
                       (when (= 2 value) (deliver reached true))
                       value))
             id (spin-core/spin-id s)]
         (is (= 1 @s))
         (let [first-run (lifetime/body-run-id ctx id)
               source-id (first @created)]
           (is (= first-run (rtp/get-state ctx [:nodes source-id :lifetime/owner])))
           (swap! source inc)
           (is (= true (deref reached 5000 ::timeout)))
           (is (= 2 @s))
           (is (= [source-id source-id] @created))
           (is (= (lifetime/body-run-id ctx id)
                  (rtp/get-state ctx [:nodes source-id :lifetime/owner]))))))))

#?(:clj
   (deftest track-reentry-has-distinct-lifetime-run
     (with-ctx [ctx]
       (let [reached (promise)
             source (sig/signal 1)
             s (spin (let [value (iv/get-new (track source))]
                       (when (= 2 value) (deliver reached true))
                       value))
             id (spin-core/spin-id s)]
         (is (= 1 @s))
         (let [before (rtp/get-state ctx [:nodes id])]
           (swap! source inc)
           (is (= true (deref reached 5000 ::timeout)))
           (is (= 2 @s))
           (let [after (rtp/get-state ctx [:nodes id])]
             (is (not= (lifetime/run-id ctx id (or (:lifetime/seq before) 1))
                       (lifetime/body-run-id ctx id)))
             (is (= (inc (or (:lifetime/seq before) 1)) (:lifetime/seq after)))
             (is (not= (:run-gen before) (:run-gen after)))
             (is (= (:lifetime/run-owner before) (:lifetime/run-owner after)))))))))

#?(:clj
   (deftest track-reentry-does-not-inherit-writers-scope
     (with-ctx [ctx]
       (let [source (sig/signal 1)
             scope (lifetime/open-scope! ctx :writer)
             created (atom nil)
             reached (promise)
             s (spin (let [value (iv/get-new (track source))
                           owned (sig/signal :owned)]
                       (reset! created (:id owned))
                       (when (= value 2) (deliver reached true))
                       value))
             id (spin-core/spin-id s)]
         (is (= 1 @s))
         (binding [ec/*owner-scope* scope]
           (swap! source inc))
         (is (= true (deref reached 5000 ::timeout)))
         (is (= 2 @s))
         (is (= (lifetime/body-run-id ctx id)
                (rtp/get-state ctx [:nodes @created :lifetime/owner])))))))

#?(:clj
   (deftest forked-await-slice-uses-child-world-run
     (with-ctx [parent-ctx]
       (let [scope (lifetime/open-scope! parent-ctx :explicit)
             source (sig/signal 1)
             created (atom nil)
             parent (binding [ec/*owner-scope* scope]
                      (spin (let [value (await (spin (iv/get-new (track source))))
                                  owned (if (= value 1)
                                          (sig/signal :first)
                                          (sig/signal :second))]
                              (reset! created (:id owned))
                              value)))
             parent-id (spin-core/spin-id parent)]
         (binding [ec/*owner-scope* scope]
           (is (= 1 @parent)))
         (let [fork (ctx/fork-context parent-ctx)]
           (binding [ec/*execution-context* fork]
             (reset! source 2)
             (simple/await-drain-complete! fork)
             (is (= 2 @parent))
             (is (= (lifetime/body-run-id fork parent-id)
                    (rtp/get-state fork [:nodes @created :lifetime/owner])))))))))
