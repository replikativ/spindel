(ns org.replikativ.spindel.lifetime.transition-catalog
  "Explicit semantic families. New model transitions require catalog and execution evidence."
  (:require [clojure.set :as set]))

(def families
  {:core #{:t01 :t02 :t03 :t04 :t05 :t06 :t07 :t08 :t09 :t10 :t11 :t12 :t13
           :t14 :t15 :t16 :t17 :t18 :t19 :t20 :t20q :t21 :t22 :t23 :t24 :t25
           :t26 :t27 :t28 :t29 :t30 :t31 :t32 :t33 :t34 :t35 :t36 :t37 :t38 :slice-enter}
   :finalization #{:finalization-wait :finalization-resume :cleanup-adopt :cleanup-claim
                   :cleanup-park :cleanup-deliver :cleanup-return :cleanup-cell}
   :computation #{:invalidate-computation :withdraw-deref :cancel-computation :signal-publish}
   :managed-cells #{:source-unreachable :reap-source}
   :deferred #{:deferred-create :deferred-request :deferred-assign :deferred-observe :deferred-protect}
   :mailbox #{:mailbox-create :mailbox-post-request :mailbox-post :mailbox-take
              :mailbox-take-now :mailbox-claim :mailbox-return :mailbox-detach}
   :operation #{:operation-start :operation-await :operation-deliver :operation-claim
                :operation-terminal :operation-return}
   :timer #{:timer-register :timer-install-result :timer-fire :timer-return :timer-handle-release}
   :release #{:release-request :release-observe :release-detach :release-notify}})

(def core-trace-transitions (set/union (:core families) (:finalization families)))
(def all-transitions (apply set/union (vals families)))
(def resource-transitions (set/difference all-transitions core-trace-transitions))

(def refusal-only
  {:operation-deliver
   {:test 'org.replikativ.spindel.lifetime.operation-model-test/standalone-delivery-cannot-invent-a-deferred-receipt
    :error :org.replikativ.spindel.lifetime.model/unsupported-operation-delivery}
   :deferred-protect
   {:test 'org.replikativ.spindel.lifetime.operation-model-test/obsolete-protection-cannot-certify-a-public-operation
    :error :org.replikativ.spindel.lifetime.model/obsolete-deferred-protection}})

(defn errors [registered]
  (let [memberships (frequencies (mapcat identity (vals families)))]
    (cond-> {}
      (not= registered all-transitions)
      (assoc :uncatalogued (set/difference registered all-transitions)
             :unregistered (set/difference all-transitions registered))
      (some #(not= 1 %) (vals memberships))
      (assoc :overlapping (into {} (filter #(not= 1 (val %)) memberships)))
      (not (set/subset? (set (keys refusal-only)) resource-transitions))
      (assoc :invalid-refusal-family (set/difference (set (keys refusal-only)) resource-transitions)))))
