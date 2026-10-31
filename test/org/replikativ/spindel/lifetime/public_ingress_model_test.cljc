(ns org.replikativ.spindel.lifetime.public-ingress-model-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [clojure.walk :as walk]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.engine.kernel :as kernel]))

(def a [:w 0])
(def b [:w 1])
(def pending-creator-retirement-actions
  [{:t :t19 :w a :v b :k :b :scope [:root a] :systems #{}}
   {:t :t04 :w b :e :owner :mode :callback}
   {:t :t01 :w b :r [:owner 1] :e :cold :tok :cold-handle :order 0}
   {:t :t04 :w a :e :waiter :mode :callback}
   {:t :t05 :w a :r [:waiter 1] :kind :await-reactive :debtor [:entity b :cold] :order 0}
   {:t :t11 :w b :r [:owner 1]}
   {:t :t37 :w b}])

(defn- semantic-view [s]
  (walk/postwalk
   (fn [x]
     (if (and (keyword? x) (#{"cancelled" "released"} (name x))
              (#{"org.replikativ.spindel.engine.kernel" "org.replikativ.spindel.lifetime.model"} (namespace x)))
       (keyword "error" (name x)) x))
   ;; Reference search-budget accounting is not runtime state. Everything else,
   ;; including diagnostics and all queues/capability metadata, is compared.
   (dissoc s :uses)))

(deftest pending-computation-outlives-its-cold-creators-row
  (doseq [cells? [false true]]
    (let [initial (m/init-state) actual (kernel/restore initial {:cells? cells?})
          states (reductions
                  (fn [before action]
                    (let [{after :state refusal :refusal} (m/attempt before action)]
                      (is (nil? refusal) (pr-str [action refusal]))
                      (kernel/step! actual action)
                      (is (= (semantic-view after) (semantic-view (kernel/snapshot actual))) (pr-str action))
                      (is (empty? (inv/check after)))
                      (is (empty? (inv/check (kernel/snapshot actual))))
                      (is (empty? (inv/edge-check {:before before :action action :after after})))
                      after)) initial pending-creator-retirement-actions)
          prefix (vec states) retired (nth prefix 6) admitted (peek prefix)]
      ;; Creator retirement really reclaims the cold entity; no ownerless row
      ;; or ordinary foreign graph edge may be kept just for the pending start.
      (is (nil? (m/ent retired b :cold)))
      (is (= [{:start-for :cold :creditor-world a :o [:o 2] :tok nil :seq 2}]
             (:queue (m/wr retired b))))
      (is (= :armed (get-in retired [:worlds a :obligations [:o 2] :slot])))
      ;; T37 consumes the admitted request's actual executable evidence and
      ;; creates a fresh Root-owned entity/Run. It never reattaches the old row.
      (is (= [:root b] (:owner (m/ent admitted b :cold))))
      (is (nil? (:creator (m/ent admitted b :cold))))
      (is (= :running (:status (m/run admitted b [:cold 1]))))
      (is (= [:root b] (:owner (m/run admitted b [:cold 1])))))))
