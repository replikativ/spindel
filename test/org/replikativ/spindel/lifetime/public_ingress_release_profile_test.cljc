(ns org.replikativ.spindel.lifetime.public-ingress-release-profile-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.engine.kernel :as kernel]))

(def a [:w 0])
(def b [:w 1])
(def d [:w 9])
(def fork {:t :t19 :w a :v b :k :child :scope [:root a] :systems #{}})
(def request {:t :release-request :w a :release [:world-release a] :reason :done})

(defn- view [state action]
  ;; The only generated enum difference in these histories is T11's default
  ;; HOST rejection diagnostic. Never rewrite application values or queues.
  (-> state
      (dissoc :uses)
      (update :events #(mapv (fn [event]
                               (if (and (= :t11 (:t action)) (not (contains? action :cancel-value))
                                        (= :host-delivery (:event event))
                                        (#{:org.replikativ.spindel.lifetime.model/cancelled
                                           :org.replikativ.spindel.engine.kernel/cancelled} (:value event)))
                                 (assoc event :value :error/cancelled) event)) %))))

(defn- checked [before action]
  (let [{after :state refusal :refusal} (m/attempt before action)]
    (is (nil? refusal) (pr-str [action refusal]))
    (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
    (is (empty? (inv/edge-check {:before before :action action :after after})) (pr-str action))
    after))

(defn- walk [initial actions]
  (let [implementations (mapv (fn [cells?]
                                [cells? (kernel/restore initial {:cells? cells?})])
                              [false true])]
    (reduce (fn [before action]
              (let [after (checked before action)]
                (doseq [[cells? implementation] implementations]
                  (let [failure (try (kernel/step! implementation action) nil
                                     (catch #?(:clj Exception :cljs :default) error
                                       (or (ex-data error) {:unexpected-exception error})))
                        actual (kernel/snapshot implementation)]
                    (is (nil? failure) (pr-str [cells? action failure]))
                    (is (= (view after action) (view actual action)) (pr-str [cells? action]))
                    (is (empty? (inv/check actual)))))
                after)) initial actions)))

(def pending-start
  [fork
   {:t :t04 :w b :e :waiter :mode :callback}
   {:t :t05 :w b :r [:waiter 1] :kind :await-reactive :debtor [:entity a :cold] :order 0}])
(def pending-host
  [{:t :t04 :w a :e :worker :mode :callback}
   fork
   {:t :t04 :w b :e :worker :mode :callback :filter {:mode :causal-follow}}])

(deftest release-routes-pending-computation-without-source-admission
  (let [before (walk (m/init-state) pending-start)
        after (walk before [request])]
    (is (nil? (m/ent before a :cold)))
    (is (= :released (:status (m/wr after a))))
    (is (= :armed (get-in after [:worlds b :obligations [:o 1] :slot])))
    (is (= [{:cancelled [:o 1] :value :done :seq 3}]
           (filterv :cancelled (:queue (m/wr after b)))))
    (is (= :releasing (get-in after [:env :releases a :phase])))))

(deftest release-routes-pending-host-at-its-original-t34-phase
  (let [before (walk (m/init-state) pending-host)
        after (walk before [request])
        deliveries (filterv #(= :host-delivery (:event %)) (:events after))]
    (is (= [:o 1] (:register-host (first (:queue (m/wr before a))))))
    (is (= [[:o 0] [:o 1]] (mapv :o deliveries)))
    (is (= [:done :done] (mapv :value deliveries)))
    (is (contains? (:host-delivered after) [a [:o 1]]))
    (is (= :released (:status (m/wr after a))))))

(defn- refusal [before]
  (let [{after :state error :refusal} (m/attempt before request)]
    (is (= ::m/unsupported-world-release (:error error)) (pr-str error))
    (is (= before after))
    (doseq [cells? [false true]]
      (let [implementation (kernel/restore before {:cells? cells?})
            original (kernel/snapshot implementation)
            error (try (kernel/step! implementation request) nil
                       (catch #?(:clj Exception :cljs :default) e
                         (or (ex-data e) {:unexpected-exception e})))]
        (is (= "unsupported-world-release" (some-> error :error name)) (pr-str error))
        (is (= original (kernel/snapshot implementation)))))))

(deftest pending-release-profile-keeps-resource-cut-and-independent-family-fences
  (testing "an actual foreign plain Deferred wait remains outside this profile"
    (refusal (walk (m/init-state)
                   [fork {:t :deferred-create :w a :e :deferred :allocation :deferred}
                    {:t :t04 :w b :e :waiter :mode :callback}
                    {:t :t05 :w b :r [:waiter 1] :kind :await-once :debtor [:entity a :deferred] :order 0}])))
  (testing "a real cut fence still prevents public release"
    ;; Kernel cuts remain unsupported. Admit this real cut in the model, then
    ;; restore that canonical checkpoint in each kernel to test release only.
    (refusal (checked (m/init-state)
                      {:t :t20 :c :cut :scope [:root a]
                       :participants {:worlds #{a} :systems #{} :components #{}}})))
  (testing "a genuinely independent Root's pending computation still needs a coordinator"
    (let [world (m/world-row d nil :root d)
          initial (-> (m/init-state) (assoc-in [:worlds d] world)
                      (update :registry conj d) (update :known-worlds conj d)
                      (assoc-in [:lineages d] (:lineage world)))]
      (refusal (walk initial [fork {:t :t04 :w b :e :waiter :mode :callback}
                              {:t :t05 :w b :r [:waiter 1] :kind :await-reactive
                               :debtor [:entity d :cold] :order 0}])))))

(deftest missing-debtor-with-committed-cancellation-is-terminal-control-only
  (let [before (walk (m/init-state)
                     [fork {:t :t04 :w a :e :creator :mode :callback}
                      {:t :deferred-create :w a :r [:creator 1] :e :deferred
                       :allocation :deferred :order 0}
                      {:t :t04 :w b :e :waiter :mode :callback}
                      {:t :t05 :w b :r [:waiter 1] :kind :await-once
                       :debtor [:entity a :deferred] :order 0}
                      {:t :t11 :w a :r [:creator 1]}])]
    ;; This is the separately disclosed foreign producer-retirement hole:
    ;; no cancellation has been committed, so public release stays refused.
    (is (nil? (:owner (m/ent before a :deferred))))
    (refusal before)
    ;; Restore a terminal transport checkpoint. The existing cancellation
    ;; committer removes the live dependency and publishes an exact packet;
    ;; this test does not decide when a Deferred producer must invoke it.
    (let [terminal (-> before (m/cancel-foreign-debtor a b [:o 2]) (m/rule-l a))
          no-authority (update-in terminal [:worlds b :queue]
                                  #(filterv (fn [event] (not= [:o 2] (:cancelled event))) %))
          after (walk terminal [request])]
      (is (nil? (m/ent terminal a :deferred)))
      (is (some #(= [:o 2] (:cancelled %)) (:queue (m/wr terminal b))))
      (is (empty? (inv/check terminal)) (pr-str (inv/check terminal)))
      (is (= :released (:status (m/wr after a))))
      (is (= :armed (get-in after [:worlds b :obligations [:o 2] :slot])))
      ;; Missing state grants no fresh body/read/producer capability by itself.
      ;; This deliberately unauthenticated checkpoint must refuse unchanged.
      (refusal no-authority))))

(deftest cancellation-upgrade-preserves-neighbors-clock-and-explicit-nil-or-false
  (doseq [reason [:done nil false ::kernel/cancelled ::m/cancelled]]
    (let [before (walk (m/init-state)
                       (into pending-start
                             [{:t :t04 :w b :e :neighbor :mode :callback}
                              {:t :t05 :w b :r [:neighbor 1] :kind :await-reactive
                               :debtor [:entity a :other] :order 0}
                              {:t :t01 :w a :e :other :tok :other-handle}
                              {:t :cancel-computation :w a :e :other :tok :other-handle :value :earlier}]))
          previous (first (:queue (m/wr before b)))
          after (walk before [(assoc request :reason reason)])
          queue (:queue (m/wr after b))
          upgraded (first (filter #(= [:o 1] (:cancelled %)) queue))]
      (is (= [:o 3] (:cancelled previous)))
      (is (= :earlier (:value previous)))
      (is (= previous (first queue)))
      (is (= 1 (count (filter #(= [:o 1] (:cancelled %)) queue))))
      (is (contains? upgraded :value))
      (is (= reason (:value upgraded)))
      (is (= [:custody-dispatch :cancelled]
             (mapv #(if (:custody-dispatch %) :custody-dispatch :cancelled) (rest queue))))
      (is (= (mapv :seq queue) (vec (range (:seq previous) (inc (:seq upgraded)))))))))

(deftest stale-start-targets-can-be-sealed-or-released-without-resurrection
  (let [pending (walk (m/init-state) pending-start)
        sealed (checked pending {:t :t26 :k :child :op :discard :kind :discard
                                 :caller (m/execution-holder a [:root a])})
        released (reduce checked sealed
                         [{:t :t27 :k :child :op :discard :steps [] :bases {} :payload :empty}
                          {:t :t29 :op :discard}])]
    ;; Ending the creditor did not consume the source's old control packet.
    (is (= [:o 1] (:o (first (:queue (m/wr sealed a))))))
    (is (nil? (get-in sealed [:worlds b :obligations [:o 1]])))
    (let [after (walk sealed [request])]
      (is (= :sealed (:status (m/wr after b))))
      (is (= :fenced (:admission (m/wr after b))))
      (is (= [:done] (mapv :value (filter :cancelled (:queue (m/wr after b)))))))
    (let [before-world (m/wr released b)
          before-clock (get-in released [:clocks b])
          after (walk released [request])]
      (is (= :released (:status before-world)))
      (is (= before-world (m/wr after b)))
      (is (= before-clock (get-in after [:clocks b])))
      (is (= :joined (get-in after [:env :releases a :phase]))))))

(deftest cut-held-starts-and-hosts-remain-outside-the-public-release-profile
  (let [before (walk (m/init-state) pending-start)
        event (first (:queue (m/wr before a)))
        held (-> before (assoc-in [:worlds a :queue] [])
                 (update-in [:env :outside] conj {:w a :event event}))]
    ;; An explicitly restored outside checkpoint is not silently discarded.
    ;; Real cut capture/permit release is a later native integration stage.
    (refusal held)))

(deftest diagnostic-view-never-normalizes-explicit-cancellation-data
  (let [native {:events [{:event :host-delivery :value ::kernel/cancelled}]}
        reference {:events [{:event :host-delivery :value ::m/cancelled}]}]
    (is (= (view native {:t :t11}) (view reference {:t :t11})))
    (doseq [action [{:t :release-request :reason ::kernel/cancelled}
                    {:t :cancel-computation :value ::kernel/cancelled}
                    {:t :t11 :cancel-value ::kernel/cancelled}]]
      (is (= native (view native action)))
      (is (not= (view native action) (view reference action))))))
