(ns org.replikativ.spindel.lifetime.operation-model-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.cps-cleanup-test :as c]))

(def w c/w)
(def n c/n)
(def op [n 1])
(def startup [op 1])
(def callback [op 2])
(def reg1 [op 1])
(def reg2 [op 2])

(defn act [s t args]
  (let [action (merge {:t t :w w :n n :op op :sequence 1 :variant :ok} args)
        after (m/step s action)]
    (is (empty? (cleanup/errors after)) (pr-str (cleanup/errors after)))
    (is (empty? (inv/operation-edge-errors {:before s :action action :after after})))
    after))

(defn source [s e]
  (m/step s {:t :deferred-create :w w :e e :allocation e :scope [:root w]}))

(defn begun []
  (-> (source (c/entered) :d1)
      (source :d2)
      (m/step {:t :finalization-wait :w w :th :worker})
      (act :operation-start {:frame startup})))

(defn read-source [s e reg frame]
  (act s :operation-await {:e e :allocation e :reg reg :frame frame :continuation reg}))

(defn assign [s e value]
  (let [s (loop [s s]
            (if (seq (:queue (m/wr s w))) (recur (m/step s {:t :queued :w w})) s))
        s (m/step s {:t :deferred-request :w w :e e :allocation e :value value})
        ev (first (:queue (m/wr s w)))
        action {:t :deferred-assign :w w :e e :allocation e :seq (:seq ev)}
        after (m/step s action)]
    (is (empty? (cleanup/errors after)) (pr-str (cleanup/errors after)))
    (is (empty? (inv/operation-edge-errors {:before s :action action :after after})))
    after))

(defn assert-transform [s]
  (let [entered (act s :operation-claim {:reg reg1 :frame callback})
        event (first (:events entered))
        terminal (act entered :operation-terminal {:value (inc (:value event))})]
    ;; Independent literal oracle: assignment 41 must enter the supplied
    ;; continuation, whose explicit test semantics select 42 as terminal.
    (is (= {:event :continuation-entry :op op :reg reg1 :continuation reg1
            :variant :ok :value 41} event))
    (is (= 42 (get-in terminal [:env :native n :delivery])))
    (is (= [{:event :operation-terminal :op op :variant :ok :value 42}] (:events terminal)))
    (is (not (cleanup/operation-barrier? (get-in terminal [:env :native n]))))
    (let [returned (act terminal :operation-return {:reg reg1 :frame callback})]
      (is (cleanup/operation-barrier? (get-in returned [:env :native n])))
      returned)))

(deftest assignment-enters-a-continuation-before-terminal-selection
  (let [waiting (read-source (begun) :d1 reg1 startup)
        returned (act waiting :operation-return {:frame startup})
        ready (assign returned :d1 41)]
    (is (= :waiting (get-in ready [:env :native n :phase])))
    (is (= :ready (get-in ready [:env :native n :operation :registrations reg1 :state])))
    (is (not (contains? (get-in ready [:env :native n]) :delivery)))
    (assert-transform ready)
    (testing "the oracle detects the old direct resource-to-parent shortcut"
      (is (seq (inv/operation-edge-errors
                {:before returned :action {:t :deferred-assign :w w :e :d1}
                 :after (-> ready (assoc-in [:env :native n :phase] :ready)
                            (assoc-in [:env :native n :delivery] 41))}))))))

(deftest already-assigned-inline-input-is-successful-data
  (doseq [value [41 nil false]]
    (let [assigned (assign (begun) :d1 value)
          waiting (read-source assigned :d1 reg1 startup)
          entered (act waiting :operation-claim {:reg reg1 :frame startup :inline? true})
          event (first (:events entered))
          terminal-value (if (= 41 value) 42 value)
          terminal (act entered :operation-terminal {:value terminal-value})
          inline-return (act terminal :operation-return {:reg reg1 :frame startup :inline? true})]
      (is (= :ok (:variant event)))
      (is (= value (:value event)))
      (is (= terminal-value (get-in terminal [:env :native n :delivery])))
      (is (= 1 (get-in inline-return [:env :native n :operation :physical])))
      (is (empty? (get-in inline-return [:env :native n :operation :registrations])))
      (act inline-return :operation-return {:frame startup}))))

(deftest sequential-waits-keep-the-operation-open
  (let [waiting (-> (begun) (read-source :d1 reg1 startup)
                    (act :operation-return {:frame startup}))
        first-ready (assign waiting :d1 41)
        entered (act first-ready :operation-claim {:reg reg1 :frame callback})
        second-wait (read-source entered :d2 reg2 callback)
        returned (act second-wait :operation-return {:reg reg1 :frame callback})
        ready (assign returned :d2 42)]
    (is (= :waiting (get-in ready [:env :native n :phase])))
    (is (= :open (get-in ready [:env :native n :operation :state])))
    (is (= #{reg2} (set (keys (get-in ready [:env :native n :operation :registrations])))))
    (is (= 2 (count (get-in ready [:env :native n :cells]))))
    (let [frame [op 3]
          entered (act ready :operation-claim {:reg reg2 :frame frame})
          terminal (act entered :operation-terminal {:value 43})]
      (is (= 42 (:value (first (:events entered)))))
      (is (= 43 (get-in terminal [:env :native n :delivery])))
      (act terminal :operation-return {:reg reg2 :frame frame}))))

(deftest two-registrations-on-one-resource-do-not-overwrite
  (let [waiting (-> (begun) (read-source :d1 reg1 startup) (read-source :d1 reg2 startup))
        ready (-> waiting (act :operation-return {:frame startup}) (assign :d1 41))
        entered (act ready :operation-claim {:reg reg1 :frame callback})
        terminal (act entered :operation-terminal {:value 42})]
    (is (= #{reg1 reg2} (set (keys (get-in waiting [:worlds w :entities :d1 :deferred :protected])))))
    (is (= #{reg1 reg2} (set (keys (get-in ready [:env :native n :operation :registrations])))))
    (is (= #{reg1} (set (keys (get-in terminal [:env :native n :operation :registrations])))))
    (is (= (dissoc terminal :events)
           (dissoc (m/step terminal {:t :cleanup-deliver :n n :sequence 1 :value :bypass}) :events)))
    (is (= (dissoc terminal :events)
           (dissoc (act terminal :operation-terminal {:value :duplicate}) :events)))
    (act terminal :operation-return {:reg reg1 :frame callback})))

(deftest startup-terminal-does-not-authorize-early-parent-resume
  (let [started (begun)
        terminal (act started :operation-terminal {:value 42})
        refused (m/attempt terminal {:t :finalization-resume :w w :n n :th :worker})]
    (is (= ::cleanup/not-ready (get-in refused [:refusal :error])))
    (is (= terminal (:state refused)))
    (let [returned (act terminal :operation-return {:frame startup})
          resumed (m/step returned {:t :finalization-resume :w w :n n :th :worker})]
      (is (nil? (get-in resumed [:env :native n]))))))

(deftest assigned-inline-continuation-entry-is-one-shot
  (let [waiting (-> (begun) (assign :d1 41) (read-source :d1 reg1 startup))
        entered (act waiting :operation-claim {:reg reg1 :frame startup :inline? true})
        duplicate {:t :operation-claim :w w :n n :op op :sequence 1
                   :reg reg1 :frame startup :inline? true}
        result (m/attempt entered duplicate)]
    (is (= ::cleanup/not-operation-ready (get-in result [:refusal :error])))
    (is (= entered (:state result)))
    (let [trace [{:before waiting :action duplicate :after entered}
                 {:before entered :action duplicate :after entered}]]
      (is (some #(= :TL1 (:id %)) (inv/check-trace trace))))))

(deftest terminal-disposition-is-independent-of-payload-shape
  (doseq [[variant value] [[:ok {:external-error :application-data}]
                           [:ok false] [:error 42] [:error nil]]]
    (let [terminal (act (begun) :operation-terminal {:variant variant :value value})]
      (is (= variant (get-in terminal [:env :native n :operation :variant])))
      (is (= value (get-in terminal [:env :native n :delivery])))
      (is (= [{:event :operation-terminal :op op :variant variant :value value}]
             (:events terminal)))))
  (let [before (begun)
        result (m/attempt before {:t :operation-terminal :w w :n n :op op :sequence 1 :value 42})]
    (is (= ::cleanup/invalid-operation-variant (get-in result [:refusal :error])))
    (is (= before (:state result)))))

(deftest assigned-inline-claim-survives-terminal-between-registration-and-entry
  (let [registered (-> (begun) (assign :d1 41) (read-source :d1 reg1 startup))
        terminal (act registered :operation-terminal {:value :first})
        entered (act terminal :operation-claim {:reg reg1 :frame startup :inline? true})
        duplicate (m/attempt entered {:t :operation-claim :w w :n n :op op :sequence 1
                                      :reg reg1 :frame startup :inline? true})
        returned (-> entered
                     (act :operation-return {:reg reg1 :frame startup :inline? true})
                     (act :operation-return {:frame startup}))]
    (is (= 41 (:value (first (:events entered)))))
    (is (= ::cleanup/not-operation-ready (get-in duplicate [:refusal :error])))
    (is (= :first (get-in returned [:env :native n :delivery])))
    (is (cleanup/operation-barrier? (get-in returned [:env :native n])))))

(deftest obsolete-protection-cannot-certify-a-public-operation
  (let [before (begun)
        action {:t :deferred-protect :w w :e :d1 :allocation :d1 :n n :sequence 1}
        result (m/attempt before action)]
    (is (= ::m/obsolete-deferred-protection (get-in result [:refusal :error])))
    (is (= before (:state result)))))

(deftest standalone-delivery-cannot-invent-a-deferred-receipt
  (let [before (read-source (begun) :d1 reg1 startup)
        action {:t :operation-deliver :w w :n n :op op :sequence 1 :reg reg1 :value 41}
        result (m/attempt before action)]
    (is (= ::m/unsupported-operation-delivery (get-in result [:refusal :error])))
    (is (= before (:state result)))))

(deftest startup-return-cannot-forget-an-assigned-inline-claim
  (let [before (-> (begun) (assign :d1 41) (read-source :d1 reg1 startup))
        action {:t :operation-return :w w :n n :op op :sequence 1 :frame startup}
        result (m/attempt before action)]
    (is (= ::cleanup/not-operation-return (get-in result [:refusal :error])))
    (is (= before (:state result)))
    (is (= 1 (get-in before [:env :native n :operation :physical])))))

(deftest callback-return-cannot-forget-a-nested-assigned-inline-claim
  (let [before (-> (begun) (assign :d2 42) (read-source :d1 reg1 startup)
                   (act :operation-return {:frame startup}) (assign :d1 41)
                   (act :operation-claim {:reg reg1 :frame callback})
                   (read-source :d2 reg2 callback))
        action {:t :operation-return :w w :n n :op op :sequence 1 :reg reg1 :frame callback}
        result (m/attempt before action)]
    (is (= ::cleanup/not-operation-return (get-in result [:refusal :error])))
    (is (= before (:state result)))
    (let [returned (-> before
                       (act :operation-claim {:reg reg2 :frame callback :inline? true})
                       (act :operation-return {:reg reg2 :frame callback :inline? true})
                       (act :operation-return {:reg reg1 :frame callback}))]
      (is (zero? (get-in returned [:env :native n :operation :physical]))))))

(deftest stale-terminal-capability-does-not-certify-a-new-outer-operation
  (let [op2 [n 2]
        resumed (-> (begun)
                    (act :operation-terminal {:value :first})
                    (act :operation-return {:frame startup})
                    (m/step {:t :finalization-resume :w w :n n :th :worker})
                    (m/step {:t :finalization-wait :w w :th :worker}))
        before (m/step resumed {:t :operation-start :w w :n n :op op2 :sequence 2 :frame [op2 1]})
        stale {:t :operation-terminal :w w :n n :op op :sequence 1 :variant :ok :value :obsolete}
        after (m/step before stale)]
    (is (= (dissoc before :events) (dissoc after :events)))
    (is (= :waiting (get-in after [:env :native n :phase])))
    (is (empty? (:events after)))
    (is (empty? (inv/operation-edge-errors {:before before :action stale :after after})))
    (is (empty? (inv/edge-check {:before before :action stale :after after})))))
