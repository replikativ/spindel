(ns org.replikativ.spindel.binding-scope-test
  "A scope macro that rebinds the execution context around an effect in a
  spin body (`with-key`, the DOM element macros) must hand the continuation
  back to the world it is RESUMED in, with only the scope put back: the
  context is supplied from outside, so a continuation resumed in a fork
  continues in the fork. Restoring the context the form was entered with
  pulled such continuations back into the original world, and a savepoint
  session whose forks ended there could never close (#64)."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [outcome (deref result 5000 ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok (first outcome)) (second outcome) (throw (second outcome))))))

(defn- keyed-model
  "Publishes one savepoint inside `with-key`, then records, in the world it
  continues in, the value it got and the key it sees after the form."
  [root]
  (binding [ec/*execution-context* root]
    (spin
     (let [v (addressing/with-key :k (sp/savepoint :test/site 0))]
       (ec/swap-state! [:test/mark] (constantly v))
       (ec/swap-state! [:test/key-after] (constantly (addressing/current-key ec/*execution-context*)))
       v))))

(deftest a-keyed-savepoint-lets-its-session-close
  (let [root (context/create-execution-context)
        session (sp/open! root {:fork-opts {:systems :none} :retain-released? false})
        ended (promise)]
    (sp/install-handlers! root {:test/site (fn [s] (sp/resume s 1))
                                sp/result-site (fn [e] (deliver ended (:savepoint/payload e)))})
    (sp/start! session (keyed-model root))
    (is (= 1 (deref ended 5000 ::timeout)))
    (is (nil? (await-cps (sp/close! session))) "the session closes")
    (is (nil? (rtp/get-state root [:test/key-after])) "the key does not leak past the form")))

(deftest a-continuation-resumed-in-a-fork-continues-in-the-fork
  (let [root (context/create-execution-context)
        session (sp/open! root {:fork-opts {:systems :none} :retain-released? false})
        worlds (atom {})
        ended (atom 0)
        done (promise)]
    (sp/install-handlers!
     root
     {:test/site (fn [s]
                   ((sp/fork s)
                    (fn [child]
                      (swap! worlds assoc :fork (:savepoint/world child) :root (:savepoint/world s))
                      (sp/resume child 2)
                      (sp/resume s 1))
                    (fn [e] (deliver done e))))
      sp/result-site (fn [_] (when (= 2 (swap! ended inc)) (deliver done :ok)))})
    (sp/start! session (keyed-model root))
    (is (= :ok (deref done 5000 ::timeout)))
    (testing "each world holds its own continuation's writes"
      (is (= 2 (rtp/get-state (:fork @worlds) [:test/mark])))
      (is (= 1 (rtp/get-state (:root @worlds) [:test/mark]))))
    (is (nil? (await-cps (sp/close! session))))))

(deftest restore-scope-tells-a-scope-from-a-world-switch
  (let [backend (Object.)
        saved {:backend backend :bindings {:dom/parent-addr :outer}}
        current {:backend (Object.) :bindings {:dom/parent-addr :inner}}]
    (testing "a scope form: keep the resuming world, put back the outer :bindings"
      (is (= (assoc current :bindings {:dom/parent-addr :outer})
             (ec/restore-scope saved current (assoc saved :bindings {:dom/parent-addr :inner})))))
    (testing "a world switch: back to the world the form left"
      (is (= saved (ec/restore-scope saved current {:backend (Object.) :bindings {}}))))))
