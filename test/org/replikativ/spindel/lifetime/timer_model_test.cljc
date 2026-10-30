(ns org.replikativ.spindel.lifetime.timer-model-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [clojure.walk :as data-walk]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.engine.kernel :as kernel]))

(def w [:w 0])
(def r [:sleeper 1])
(def o [:o 1])
(def n [:timer w o])
(def frame [:timer-frame n 0])
(defn row [s] (get-in s [:env :native n]))
(def register {:t :timer-register :w w :r r :o o :n n :th :engine :order 0 :delay-ms 10 :value 41})
(def seated {:t :timer-install-result :w w :n n :variant :ok :handle? true})
(def no-handle (assoc seated :handle? false))
(def fired {:t :timer-fire :w w :n n :frame frame :variant :ok :value 41})
(def returned {:t :timer-return :w w :n n :frame frame})
(def release-claim {:t :timer-handle-release :w w :n n :phase :claim})
(def release-return {:t :timer-handle-release :w w :n n :phase :returned :variant :ok})
(def slice-return {:t :t38 :th :engine})
(def cancel {:t :t11 :w w :r r})
(def prefix [{:t :t04 :w w :e :sleeper :mode :deref}
             {:t :slice-enter :w w :r r :th :engine}])

(defn snapshot-view [state]
  (data-walk/postwalk
   (fn [value]
     (if (and (keyword? value) (#{"cancelled" "released"} (name value))
              (#{"org.replikativ.spindel.engine.kernel" "org.replikativ.spindel.lifetime.model"} (namespace value)))
       (keyword "error" (name value)) value))
   (select-keys state [:worlds :env :serial :events :clocks :registry :generation-clock])))

(defn walk
  ([actions] (walk (m/init-state {:slices? true}) actions))
  ([initial actions]
   (let [implementations (mapv #(kernel/restore initial {:cells? %}) [false true])]
     (vec
      (reductions
       (fn [before item]
         (let [action (if (fn? item) (item before) item)
               {after :state :keys [refusal observation]} (m/attempt before action)
               edge {:before before :action action :after after :refusal refusal :observation observation}]
           (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
           (is (empty? (inv/edge-check edge)) (pr-str [action (inv/edge-check edge)]))
           (doseq [implementation implementations]
             (let [error (try (kernel/step! implementation action) nil
                              (catch #?(:clj Exception :cljs :default) error (ex-data error)))]
               (is (= (some-> refusal :error name) (some-> error :error name)) (pr-str [action refusal error]))
               (is (= (snapshot-view after) (snapshot-view (kernel/snapshot implementation))) (pr-str action))))
           after)) initial actions)))))

(defn registered [] (peek (walk (conj prefix register))))
(defn refusal [state action error]
  (let [attempt (m/attempt state action)]
    (is (= error (get-in attempt [:refusal :error])) (pr-str attempt))
    (is (= state (:state attempt)))
    (walk state [action])))

(deftest ordinary-timer-preserves-successful-data-and-the-body-transforms-it
  (doseq [value [nil false {:failure :data} 41]]
    (let [states (walk (into prefix [(assoc register :value value) seated slice-return
                                     (assoc fired :value value) returned release-claim release-return
                                     {:t :slice-enter :w w :r r :th :engine}
                                     {:t :t07 :w w :r r :value [:transformed value]}
                                     slice-return]))
          entries (filter #(= :timer-entry (:event %)) (mapcat :events states))]
      (is (= [value] (mapv :value entries)))
      (is (= [:ok] (mapv :variant entries)))
      (is (= [:transformed value] (:result (m/ent (peek states) w :sleeper))))
      (is (nil? (row (peek states)))))))

(deftest cancellation-closes-entry-before-late-installation-and-disposal
  (let [initial (registered)
        cancelled (peek (walk initial [cancel]))
        late (peek (walk cancelled [seated]))]
    (is (= :revoked (:phase (row cancelled))))
    (is (not (contains? (row cancelled) :value)))
    (is (= :unwinding (:status (m/run cancelled w r))))
    (is (false? (m/join-ready? cancelled w r)))
    (is (= :release-pending (:handle (row late))))
    (let [end (peek (walk late [fired release-claim release-return]))]
      (is (nil? (row end)))
      (is (false? (m/join-ready? end w r)))
      (is (m/join-ready? (peek (walk end [slice-return])) w r)))))

(deftest fire-before-ticket-does-not-confuse-install-result-with-physical-return
  (let [initial (registered)
        entered (peek (walk initial [fired]))
        end (peek (walk entered [seated release-claim release-return cancel]))]
    (is (= #{frame} (:frames (row entered))))
    (is (= :fired (:phase (row entered))))
    (is (false? (m/join-ready? end w r)))
    (let [callback-returned (peek (walk end [returned]))]
      (is (nil? (row callback-returned)))
      (is (false? (m/join-ready? callback-returned w r)))
      (is (m/join-ready? (peek (walk callback-returned [slice-return])) w r)))))

(deftest duplicate-and-stale-cap-free-wrappers-cannot-reenter
  (let [initial (peek (walk (registered) [no-handle slice-return fired]))
        duplicate (peek (walk initial [fired (assoc fired :variant :error :value :submission-error)]))]
    (is (= (dissoc initial :events) (dissoc duplicate :events)))
    (is (empty? (:events duplicate)))
    (let [end (peek (walk duplicate [returned]))]
      (is (nil? (row end)))
      (is (= (dissoc end :events) (dissoc (peek (walk end [fired])) :events))))))

(deftest all-failure-dispositions-are-explicit-and-do-not-infer-payload-shape
  (let [install-error {:t :timer-install-result :w w :n n :variant :error :handle? false :value false}
        states (walk (registered) [install-error])]
    (is (= [false] (mapv :value (filter #(= :resume (:event %)) (:events (peek states))))))
    (is (nil? (row (peek states)))))
  (let [failed (peek (walk (registered) [no-handle slice-return (assoc fired :variant :error :value 41)]))]
    (is (= :failed (:phase (row failed))))
    (is (= [{:event :timer-entry :world w :n n :r r :o o :frame frame :variant :error :value 41}]
           (filterv #(= :timer-entry (:event %)) (:events failed))))
    (walk failed [returned]))
  (let [late (peek (walk (registered) [fired {:t :timer-install-result :w w :n n :variant :error
                                              :handle? false :value :late-error}]))]
    (is (= :fired (:phase (row late))))
    (is (= [:install] (mapv :stage (filter #(= :timer-fault (:event %)) (:events late)))))
    (walk late [returned])))

(deftest failed-disposal-reports-fault-and-releases-engine-captures-without-os-release-claim
  (let [end (peek (walk (registered) [seated cancel release-claim
                                      (assoc release-return :variant :error :value :cancel-failed)]))]
    (is (nil? (row end)))
    (is (= [{:event :timer-fault :world w :n n :stage :release :value :cancel-failed}]
           (filterv #(= :timer-fault (:event %)) (:events end))))
    (is (false? (m/join-ready? end w r)))
    (walk end [slice-return fired])))

(deftest typed-waits-refuse-generic-resume-and-unfenced-receipts-without-mutation
  (let [initial (registered)]
    (refusal initial {:t :t06 :w w :o o :value :forged} ::m/unsupported-timer-resume)
    (refusal initial {:t :t35 :th :host :op {:kind :resume :w w :o o :value :forged}}
             ::m/unsupported-timer-resume)
    (refusal initial (assoc fired :value :forged) ::m/not-timer-value)
    (refusal initial returned ::m/not-timer-return)
    (refusal initial slice-return ::m/timer-install-pending)
    (refusal initial release-return ::m/not-timer-handle-release)
    (refusal initial {:t :native-progress :n n :state :joined} ::m/protected-cleanup)
    (refusal initial (assoc seated :variant :unknown) ::m/not-timer-install)
    (refusal initial (assoc fired :variant :unknown) ::m/not-timer-fire)
    (doseq [t [:t20 :t20q]]
      (refusal initial {:t t :c :timer-cut :scope [:root w]
                        :participants {:worlds #{w} :components #{} :systems #{}}}
               ::m/unsupported-timer-cut)))
  (let [claimed (peek (walk (registered) [seated cancel release-claim]))]
    (refusal claimed release-claim ::m/not-timer-handle-release)))

(deftest stale-generation-timer-cannot-wake-the-new-copy
  (let [initial (registered)
        reentered (peek (walk initial [{:t :t09 :w w :e :sleeper :cause :track :order -1}]))
        after (peek (walk reentered [fired]))]
    (is (= [:sleeper 2] (m/current after w :sleeper)))
    (is (= :revoked (:phase (row after))))
    (is (= :running (:status (m/run after w [:sleeper 2]))))
    (is (empty? (:events after)))
    (walk after [seated release-claim release-return slice-return])))

(deftest callback-frames-and-install-receipts-are-independently-conserved
  (let [initial (registered)
        entered (peek (walk initial [fired]))
        erased (update-in entered [:env :native] dissoc n)
        entry-edge {:before initial :action fired :after entered}]
    (is (seq (inv/timer-edge-errors (assoc entry-edge :after erased))))
    (is (seq (inv/timer-edge-errors {:before entered :action {:t :t17 :w w} :after erased})))
    (is (seq (inv/timer-errors (assoc-in entered [:env :native n :value] :leak))))
    (is (seq (inv/timer-edge-errors (assoc entry-edge :after (assoc entered :events [])))))))

(deftest live-prefix-adoption-updates-timer-ancestry-then-retirement-freezes-it
  (let [parent [:parent 1] successor [:parent 2]
        timer-o [:o 2] timer-n [:timer w timer-o] timer-frame [:timer-frame timer-n 0]
        started (peek (walk [{:t :t04 :w w :e :parent :mode :deref}
                             {:t :t01 :w w :scope parent :e :sleeper :order 0}
                             {:t :t04 :w w :scope parent :e :sleeper :mode :deref}
                             {:t :slice-enter :w w :r r :th :engine}
                             (assoc register :o timer-o :n timer-n)
                             (assoc seated :n timer-n)]))
        adopted (peek (walk started [{:t :t09 :w w :e :parent :cause :track :order 1}]))
        receipt (get-in adopted [:env :native timer-n])
        retired (peek (walk adopted [{:t :t11 :w w :r successor}]))
        old-anchor (:anchor (get-in retired [:env :native timer-n]))]
    (is (= successor (:owner (m/run adopted w r))))
    (is (= [w r] (:owner receipt)))
    (is (some #{successor} (:anchor receipt)))
    (is (not-any? #{parent} (:anchor receipt)))
    (is (= :revoked (get-in retired [:env :native timer-n :phase])))
    (is (true? (get-in retired [:env :native timer-n :retired?])))
    (is (some #{successor} old-anchor))
    (let [disposed (peek (walk retired [(assoc release-claim :n timer-n)
                                        (assoc release-return :n timer-n)]))]
      (is (nil? (get-in disposed [:env :native timer-n])))
      (is (false? (m/join-ready? disposed w successor)))
      (is (m/join-ready? (peek (walk disposed [slice-return])) w successor)))))

(deftest timer-alphabet-exhausts-one-registration-with-independent-safety-checks
  (let [initial (assoc-in (registered) [:model :timers?] true)
        canonical #(dissoc % :events)]
    (loop [todo [initial] index 0 seen #{(canonical initial)} edges 0]
      (if (= index (count todo))
        (do (is (> (count seen) 10)) (is (> edges (count seen))))
        (let [before (nth todo index)
              actions (concat (m/timer-enabled before)
                              (when (m/work? (m/run before w r)) [cancel])
                              (when (get-in before [:env :threads :engine :run]) [slice-return]))
              [todo seen edges]
              (reduce
               (fn [[todo seen edges] action]
                 (let [{after :state :keys [refusal observation]} (m/attempt before action)
                       key (canonical after)]
                   (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
                   (is (empty? (inv/edge-check {:before before :action action :after after
                                                :refusal refusal :observation observation})))
                   (if (contains? seen key) [todo seen (inc edges)]
                       [(conj todo after) (conj seen key) (inc edges)])))
               [todo seen edges] actions)]
          (is (< (count seen) 2000) "The finite timer-only alphabet must terminate")
          (when (< (count seen) 2000) (recur todo (inc index) seen edges)))))))

(deftest typed-resource-cut-fences-refuse-without-changing-authority
  (let [initial (m/init-state {:slices? true :cps-exit? true})
        operation-ticket (cleanup/ticket w r) operation [operation-ticket 1]
        operation-state (reduce m/step initial
                                (into prefix [{:t :finalization-wait :w w :th :engine}
                                              {:t :operation-start :w w :n operation-ticket :op operation
                                               :sequence 1 :frame [operation 1]}]))
        deferred (m/step initial {:t :deferred-create :w w :e :d :allocation :d})
        mailbox (m/step initial {:t :mailbox-create :w w :e :mb :allocation :mb})]
    (doseq [before [deferred mailbox operation-state] t [:t20 :t20q]]
      (refusal before {:t t :c :resource-cut :scope [:root w]
                       :participants {:worlds #{w} :components #{} :systems #{}}}
               ::m/unsupported-resource-cut))))

(deftest true-process-loss-drops-volatile-resources-and-preserves-durable-recovery
  ;; T31 models actual process loss, not graceful world shutdown or copying.
  ;; The concrete kernel has no crash adapter; these are symbolic-only edges.
  (let [base (m/step (m/init-state {:slices? true :cps-exit? true})
                     {:t :t19 :w w :v [:w 1] :k :durable-fork :scope [:root w] :systems #{:a}})
        timer (reduce m/step base (conj prefix register))
        active-timer (m/step timer fired)
        deferred (m/step base {:t :deferred-create :w w :e :d :allocation :d})
        mailbox (m/step base {:t :mailbox-create :w w :e :mb :allocation :mb})
        ticket (cleanup/ticket w r) operation [ticket 1]
        protected (reduce m/step base
                          (into prefix [{:t :finalization-wait :w w :th :engine}
                                        {:t :operation-start :w w :n ticket :op operation
                                         :sequence 1 :frame [operation 1]}]))
        crash {:t :t31 :phase :crash} restart {:t :t31 :phase :restart}
        expected-recovery (:durable (m/step (m/step base crash) restart))]
    (is (seq (get-in base [:durable :caps])))
    (doseq [before [timer active-timer deferred mailbox protected]]
      (let [lost (m/step before crash) recovered (m/step lost restart)]
        (is (empty? (:worlds lost)))
        (is (empty? (get-in lost [:env :native])))
        (is (empty? (get-in lost [:env :threads])))
        (is (= (:durable before) (:durable lost)))
        (is (= expected-recovery (:durable recovered)))
        (is (empty? (inv/check lost)))
        (is (empty? (inv/edge-check {:before before :action crash :after lost})))
        (is (empty? (inv/check recovered)))
        (is (empty? (inv/edge-check {:before lost :action restart :after recovered})))))
    ;; Restart is not a second process-loss exemption: inventing removal there
    ;; cannot erase an already admitted timer callback frame.
    (is (seq (inv/timer-edge-errors {:before active-timer :action restart
                                     :after (update-in active-timer [:env :native] dissoc n)})))))
