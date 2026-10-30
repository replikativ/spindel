(ns org.replikativ.spindel.engine.computation-invalidation-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [clojure.walk :as walk]
            [org.replikativ.spindel.engine.kernel :as kernel]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.model :as m]))

(def w [:w 0])
(def r [:target 1])
(def invalidate {:t :invalidate-computation :w w :e :target})

(defn- view [state]
  (walk/postwalk
   (fn [x]
     (if (and (keyword? x) (#{"cancelled" "released"} (name x))
              (#{"org.replikativ.spindel.engine.kernel"
                 "org.replikativ.spindel.lifetime.model"} (namespace x)))
       (keyword "error" (name x)) x))
   (select-keys state [:worlds :env :serial :events :generation-clock :clocks
                       :host-delivered :registry :caps :durable :known-worlds
                       :lineages :cuts :records])))

(defn- checked-walk! [initial actions]
  ;; Both stores persist across the whole trace: restore must not repair an
  ;; index between a constructor invalidation and the ensuing completion.
  (let [kernels (mapv #(kernel/restore initial {:cells? %}) [false true])]
    (vec
     (reductions
      (fn [before action]
        (let [{after :state :keys [refusal observation]} (m/attempt before action)]
          (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
          (is (empty? (inv/edge-check {:before before :action action :after after
                                       :refusal refusal :observation observation}))
              (pr-str action))
          (doseq [actual kernels]
            (let [error (try (kernel/step! actual action) nil
                             (catch #?(:clj Exception :cljs :default) ex (ex-data ex)))]
              (is (= (some-> refusal :error name) (some-> error :error name))
                  (pr-str [action refusal error]))
              (is (= (view after) (view (kernel/snapshot actual))) (pr-str action))))
          after))
      initial actions))))

(def setup-actions
  [{:t :t02 :w w :e :source :value 0}
   {:t :t04 :w w :e :target :mode :callback :host :first}
   {:t :t04 :w w :e :observer :mode :callback :host :observer}
   {:t :t05 :w w :r [:observer 1] :kind :await-reactive :debtor [:entity w :target]}
   {:t :t05 :w w :r r :kind :track :debtor [:entity w :source]}])

(defn- incoming [state e]
  (into {} (filter #(= [:entity w e] (:debtor (val %))))
        (get-in state [:worlds w :obligations])))

(deftest invalidation-is-lazy-and-retains-observers-and-outgoing-work
  (let [states (checked-walk! (m/init-state) (into setup-actions [invalidate invalidate]))
        before (nth states (count setup-actions))
        invalidated (nth states (inc (count setup-actions)))
        twice (peek states)]
    (is (= :running (:status (m/run invalidated w r))))
    (is (= (-> before
               (assoc :events [])
               (assoc-in [:worlds w :entities :target :dirty?] true)
               (assoc-in [:worlds w :runs r :validation-lost?] true))
           invalidated)
        "Only validation changes: no body entry, cancellation, queue or graph mutation")
    (is (= (incoming before :target) (incoming invalidated :target)))
    (is (= invalidated twice))))

(deftest invalidated-completion-is-dirty-and-cold-successor-fences-old-completion
  (let [states (checked-walk!
                (m/init-state)
                (into setup-actions
                      [invalidate
                       {:t :t07 :w w :r r :value :old}
                       {:t :t09 :w w :e :target :cause :dirty :order -1}
                       {:t :t07 :w w :r r :value :late-old}
                       {:t :t07 :w w :r [:target 2] :value :fresh}]))
        old-completed (nth states (+ (count setup-actions) 2))
        successor (nth states (+ (count setup-actions) 3))
        late-old (nth states (+ (count setup-actions) 4))
        fresh (peek states)]
    (is (= :old (:result (m/ent old-completed w :target))))
    (is (true? (:dirty? (m/ent old-completed w :target))))
    (is (= [:target 2] (m/current successor w :target)))
    (is (= (dissoc successor :events) (dissoc late-old :events)))
    (is (= :fresh (:result (m/ent fresh w :target))))
    (is (false? (:dirty? (m/ent fresh w :target))))))

(deftest parked-invalidation-keeps-t04-joining-until-explicit-cold-t09
  (let [actions [{:t :t04 :w w :e :target :mode :callback :host :first}
                 {:t :t05 :w w :r r :kind :await-once :debtor [:host :gate]}
                 invalidate
                 {:t :t04 :w w :e :target :mode :callback :host :second}
                 {:t :t09 :w w :e :target :cause :dirty :order -1}
                 {:t :t07 :w w :r r :value :late-old}
                 {:t :t07 :w w :r [:target 2] :value :fresh}]
        states (checked-walk! (m/init-state) actions)
        invalidated (nth states 3)
        joined (nth states 4)
        successor (nth states 5)
        late-old (nth states 6)]
    (is (= :parked (:status (m/run invalidated w r))))
    (is (= r (m/current joined w :target)))
    (is (= :parked (:status (m/run joined w r))))
    (is (= 2 (count (incoming joined :target))))
    (is (= (incoming joined :target) (incoming successor :target)))
    (is (= [:target 2] (m/current successor w :target)))
    (is (= (dissoc successor :events) (dissoc late-old :events)))))

(deftest an-unstarted-owned-spin-can-be-invalidated-without-starting-it
  (let [states (checked-walk! (m/init-state)
                              [{:t :t04 :w w :e :owner :mode :callback}
                               {:t :t01 :w w :scope [:owner 1] :e :target}
                               invalidate])
        before (nth states 2) after (peek states)]
    (is (nil? (m/current after w :target)))
    (is (true? (:dirty? (m/ent after w :target))))
    (is (= (get-in before [:worlds w :runs]) (get-in after [:worlds w :runs])))))

(deftest invalidation-refusals-preserve-admission-and-managed-source-authority
  (let [source (last (checked-walk!
                      (m/init-state)
                      [{:t :t02 :w w :e :cell :kind :atom :allocation :allocation :value 42}
                       {:t :source-unreachable :w w :e :cell :allocation :allocation}]))
        running (reduce m/step (m/init-state) setup-actions)
        fenced (m/step running {:t :t20 :c :cut :scope [:root w]
                                :participants {:worlds #{w} :systems #{}}})
        released (m/step (m/init-state) {:t :t34 :w w})]
    (doseq [[before action error]
            [[source (assoc invalidate :e :cell) ::m/not-computation]
             [(m/init-state) invalidate ::m/not-computation]
             [fenced invalidate ::m/not-admitted]
             [released invalidate ::m/not-live]]]
      (is (= error (get-in (m/attempt before action) [:refusal :error])))
      (is (= before (last (checked-walk! before [action])))))))

(deftest cancelled-slices-and-protected-cleanup-cannot-invalidate-ordinary-work
  (let [initial (m/init-state {:slices? true :cps-exit? true})
        cancelled (last (checked-walk!
                         initial [{:t :t04 :w w :e :target :mode :callback}
                                  {:t :slice-enter :w w :r r :th :worker}
                                  {:t :t02 :w w :scope r :e :cell :kind :atom :value :retained}
                                  {:t :t11 :w w :r r}]))
        action (assoc invalidate :th :worker)
        n (cleanup/ticket w r)]
    (is (= ::m/cancelled (get-in (m/attempt cancelled action) [:refusal :error])))
    (is (= cancelled (last (checked-walk! cancelled [action]))))
    (let [claimed (last (checked-walk! cancelled
                                       [{:t :t38 :th :worker}
                                        {:t :cleanup-claim :n n :th :cleaner}]))
          action (assoc invalidate :th :cleaner)]
      ;; Ordinary construction/invalidation is rejected by the retired-slice
      ;; guard before the narrower cleanup-operation allowlist is consulted.
      (is (= ::m/cancelled (get-in (m/attempt claimed action) [:refusal :error])))
      (is (= claimed (last (checked-walk! claimed [action])))))))

(def deref-actions
  [{:t :t01 :w w :e :target :tok :handle}
   {:t :t04 :w w :e :target :tok :handle :mode :deref}])
(def withdraw {:t :withdraw-deref :w w :o [:o 0]})

(deftest withdrawing-a-deref-observer-leaves-the-body-running-and-its-cache-intact
  (let [states (checked-walk!
                (m/init-state)
                (into deref-actions
                      [withdraw withdraw
                       {:t :t07 :w w :r r :value :finished}
                       {:t :t08 :w w :e :target :value :finished}]))
        before (nth states 2)
        withdrawn (nth states 3)
        duplicate (nth states 4)
        finished (peek states)]
    (is (= (m/run before w r) (m/run withdrawn w r)))
    (is (= :running (:status (m/run withdrawn w r))))
    (is (= (m/ent before w :target) (m/ent withdrawn w :target)))
    (is (empty? (incoming withdrawn :target)))
    (is (= [:creditor-cancelled] (mapv :cause (:events withdrawn))))
    (is (= (dissoc withdrawn :events) (dissoc duplicate :events)))
    (is (= :finished (:result (m/ent finished w :target))))
    (is (true? (:completed? (m/ent finished w :target))))
    (is (empty? (incoming finished :target)))
    (is (not-any? #(= :host-delivery (:event %)) (:events finished)))))

(deftest withdrawal-before-host-delivery-wins-but-served-withdrawal-is-inert
  (let [before-delivery
        (checked-walk! (m/init-state)
                       (into deref-actions
                             [{:t :t07 :w w :r r :value :finished}
                              withdraw
                              {:t :t08 :w w :e :target :value :finished}]))
        served (checked-walk! (m/init-state)
                              (into deref-actions
                                    [{:t :t07 :w w :r r :value :finished}
                                     {:t :t08 :w w :e :target :value :finished}
                                     withdraw]))
        delivery (nth served 4)
        after-withdrawal (peek served)]
    (is (not-any? #(= :host-delivery (:event %)) (:events (peek before-delivery))))
    (is (= 1 (count (filter #(= :host-delivery (:event %)) (:events delivery)))))
    (is (empty? (incoming delivery :target)))
    (is (= (dissoc delivery :events) (dissoc after-withdrawal :events)))
    (is (= :finished (:result (m/ent after-withdrawal w :target))))))

(deftest withdrawal-refuses-callback-and-run-owned-obligations
  (let [callback (last (checked-walk! (m/init-state)
                                      [{:t :t04 :w w :e :target :mode :callback}]))
        run-owned (last (checked-walk! (m/init-state)
                                       [{:t :t04 :w w :e :target :mode :callback}
                                        {:t :t05 :w w :r r :kind :await-once :debtor [:host :gate]}]))]
    (doseq [[before action] [[callback withdraw] [run-owned (assoc withdraw :o [:o 1])]]]
      (is (= ::m/not-host-deref (get-in (m/attempt before action) [:refusal :error])))
      (is (= before (last (checked-walk! before [action])))))))

(deftest withdrawal-obeys-fenced-admission-and-missing-observer-idempotence
  (let [before (reduce m/step (m/init-state) deref-actions)
        fenced (m/step before {:t :t20 :c :cut :scope [:root w]
                               :participants {:worlds #{w} :systems #{}}})
        quiescent (m/step (m/init-state)
                          {:t :t20q :c :cut :scope [:root w]
                           :participants {:worlds #{w} :systems #{}}})
        missing (assoc withdraw :o [:o 99])]
    (is (= ::m/not-admitted (get-in (m/attempt fenced withdraw) [:refusal :error])))
    (is (= fenced (last (checked-walk! fenced [withdraw]))))
    (is (= (dissoc before :events)
           (dissoc (last (checked-walk! before [missing missing])) :events)))
    (is (= ::m/not-admitted (get-in (m/attempt quiescent missing) [:refusal :error])))
    (is (= quiescent (last (checked-walk! quiescent [missing]))))))
