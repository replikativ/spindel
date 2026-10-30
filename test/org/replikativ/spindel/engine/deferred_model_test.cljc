(ns org.replikativ.spindel.engine.deferred-model-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [clojure.walk :as walk]
            [org.replikativ.spindel.engine.kernel :as kernel]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.lifetime.invariants :as inv]))

(def w [:w 0])
(def r [:worker 1])
(def n (cleanup/ticket w r))
(def cell [w r :d])
(def create {:t :deferred-create :w w :e :d :allocation :d})
(defn- request [value claim?] {:t :deferred-request :w w :e :d :allocation :d :value value :claim? claim?})
(defn- assign-front [s]
  (let [event (or (first (:queue (m/wr s w)))
                  (:event (first (filter #(= w (:w %)) (get-in s [:env :outside])))))]
    (assoc (dissoc event :deferred-assignment) :t :deferred-assign :w w :e (:deferred-assignment event))))
(defn- view [state]
  (walk/postwalk
   (fn [value]
     (if (and (keyword? value) (#{"cancelled" "released"} (name value))
              (#{"org.replikativ.spindel.engine.kernel" "org.replikativ.spindel.lifetime.model"} (namespace value)))
       (keyword "error" (name value)) value))
   (select-keys state [:worlds :env :serial :events :clocks :generation-clock :registry])))

(defn- checked-walk!
  ([actions] (checked-walk! (m/init-state) actions))
  ([initial actions]
   (let [actuals (mapv #(kernel/restore initial {:cells? %}) [false true])]
     (vec
      (reductions
       (fn [before action]
         (let [action (if (fn? action) (action before) action)
               {after :state :keys [refusal observation]} (m/attempt before action)]
           (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
           (is (empty? (inv/edge-check {:before before :action action :after after
                                        :refusal refusal :observation observation})) (pr-str action))
           (doseq [actual actuals]
             (let [error (try (kernel/step! actual action) nil
                              (catch #?(:clj Exception :cljs :default) e (ex-data e)))]
               (is (= (some-> refusal :error name) (some-> error :error name)) (pr-str [action refusal error]))
               (is (= (view after) (view (kernel/snapshot actual))) (pr-str action))))
           after)) initial actions)))))

(deftest claim-is-independent-of-assignment-and-first-queued-attempt-wins
  (doseq [value [nil false {:throwable-as-data :ordinary-value}]]
    (let [states (checked-walk! [create (request value false) (request :claimed true)
                                 (request :lost true) assign-front assign-front])
          requested (nth states 3) loser (nth states 4)
          assigned (nth states 5) final (peek states)]
      (is (= false (:completed? (m/ent requested w :d))))
      (is (= true (get-in requested [:worlds w :entities :d :deferred :claimed?])))
      (is (= 2 (count (:queue (m/wr requested w)))))
      (is (= (dissoc requested :events) (dissoc loser :events)))
      (is (true? (:completed? (m/ent assigned w :d))))
      (is (= value (:result (m/ent assigned w :d))))
      (is (= value (:result (m/ent final w :d))))
      (is (= 1 (count (:queue (m/wr final w)))))
      (is (= value (:value (first (:queue (m/wr final w)))))))))

(deftest assignment-before-first-claim-still-allows-exactly-one-claim
  (let [states (checked-walk! [create (request :first false) assign-front
                               {:t :t08 :w w :e :d :value :first}
                               (request :later true) (request :lost true) assign-front])
        claimed (nth states 5) final (peek states)]
    (is (true? (get-in claimed [:worlds w :entities :d :deferred :claimed?])))
    (is (= 1 (count (:queue (m/wr claimed w)))))
    (is (= :first (:result (m/ent final w :d))))
    (is (empty? (:queue (m/wr final w))))))

(deftest pending-await-creates-no-deferred-run-and-cancellation-removes-the-reader
  (let [states (checked-walk! [create {:t :t04 :w w :e :worker :mode :callback}
                               {:t :t05 :w w :r r :kind :await-once :debtor [:entity w :d]}
                               {:t :t11 :w w :r r}
                               (request false true) assign-front])
        parked (nth states 3) cancelled (nth states 4) assigned (peek states)]
    (is (= :parked (:status (m/run parked w r))))
    (is (nil? (m/current parked w :d)))
    (is (= :armed (get-in parked [:worlds w :obligations [:o 1] :slot])))
    (is (nil? (get-in cancelled [:worlds w :obligations [:o 1]])))
    (is (true? (:completed? (m/ent assigned w :d))))
    (is (false? (:result (m/ent assigned w :d))))
    (is (nil? (m/current assigned w :d)))))

(deftest assigned-await-and-host-observation-are-inline-without-extra-registration
  (let [states (checked-walk! [create {:t :deferred-observe :w w :e :d :allocation :d}
                               (request 7 false) assign-front
                               {:t :t08 :w w :e :d :value 7}
                               {:t :deferred-observe :w w :e :d :allocation :d}
                               {:t :t04 :w w :e :worker :mode :callback}
                               {:t :t05 :w w :r r :kind :await-once :debtor [:entity w :d]}])
        pending (nth states 2) delivered (nth states 5) observed (nth states 6) final (peek states)]
    (is (= :deref (get-in pending [:worlds w :obligations [:o 0] :kind])))
    (is (= [7] (mapv :value (filter #(= :host-delivery (:event %)) (:events delivered)))))
    (is (= [7] (mapv :value (filter #(= :host-delivery (:event %)) (:events observed)))))
    (is (= :running (:status (m/run final w r))))
    (is (= [:inline-resume] (mapv :event (:events final))))
    (is (nil? (m/current final w :d)))))

(defn- protected-actions []
  [{:t :t04 :w w :e :worker :mode :callback}
   {:t :slice-enter :w w :r r :th :thread}
   (assoc create :scope r)
   {:t :finalization-wait :w w :th :thread}
   {:t :deferred-protect :w w :e :d :allocation :d :n n :sequence 1 :th :thread}
   {:t :t38 :th :thread}
   {:t :t11 :w w :r r}])

(deftest protected-retained-assignment-delivers-the-wait-without-ordinary-publication
  (let [states (checked-walk! (m/init-state {:slices? true :cps-exit? true})
                              (into (protected-actions)
                                    [(assoc (request :ack true) :cell cell) assign-front]))
        retired (nth states 7) final (peek states)]
    (is (nil? (m/ent retired w :d)))
    (is (= {:kind :deferred :result nil :allocation :d
            :deferred {:assigned? false :claimed? false :protected {n 1}} :holders #{n}}
           (get-in retired [:env :cleanup-cells cell])))
    (is (= :ready (get-in final [:env :native n :phase])))
    (is (= :ack (get-in final [:env :native n :delivery])))
    (is (= {:assigned? true :claimed? true :protected {}}
           (get-in final [:env :cleanup-cells cell :deferred])))
    (is (= :ack (get-in final [:env :cleanup-cells cell :result])))
    (is (empty? (:queue (m/wr final w))))))

(deftest stale-deliveries-are-inert-and-unrelated-readiness-clears-the-registration
  (let [initial (reduce m/step (m/init-state {:slices? true :cps-exit? true}) (protected-actions))
        states (checked-walk! initial
                              [{:t :cleanup-deliver :n n :sequence 0 :value :obsolete}
                               {:t :cleanup-deliver :n n :sequence 1 :value {:external-error :rejected}}
                               (assoc (request :ack false) :cell cell) assign-front])
        stale (nth states 1) ready (nth states 2) final (peek states)]
    (is (= (dissoc initial :events) (dissoc stale :events)))
    (is (= {} (get-in ready [:env :cleanup-cells cell :deferred :protected])))
    (is (nil? (get-in ready [:env :native n :deferred-wait])))
    (is (= {:external-error :rejected} (get-in final [:env :native n :delivery])))
    (is (true? (get-in final [:env :cleanup-cells cell :deferred :assigned?])))))

(deftest queued-live-attempt-survives-retirement-and-finds-the-exact-retained-allocation
  (let [actions (vec (concat (take 6 (protected-actions))
                             [(request :ack false) {:t :t11 :w w :r r} assign-front]))
        states (checked-walk! (m/init-state {:slices? true :cps-exit? true}) actions)
        retired (nth states 8) final (peek states)]
    (is (nil? (m/ent retired w :d)))
    (is (= 1 (count (:queue (m/wr retired w)))))
    (is (nil? (:cell (first (:queue (m/wr retired w))))))
    (is (= :ack (get-in final [:env :cleanup-cells cell :result])))
    (is (= :ready (get-in final [:env :native n :phase])))))

(deftest queued-attempts-block-host-gc-until-assignment-publication-is-served
  (let [states (checked-walk! [create (request :value false)
                               {:t :source-unreachable :w w :e :d :allocation :d}])
        pending (peek states)
        refused (m/attempt pending {:t :reap-source :w w :e :d :allocation :d})]
    (is (= ::m/source-in-use (get-in refused [:refusal :error])))
    (checked-walk! pending [{:t :reap-source :w w :e :d :allocation :d}])
    (let [assigned (m/step pending (assign-front pending))]
      (is (= ::m/source-in-use
             (get-in (m/attempt assigned {:t :reap-source :w w :e :d :allocation :d}) [:refusal :error])))
      (let [final (peek (checked-walk! pending [assign-front {:t :t08 :w w :e :d :value :value}
                                                {:t :reap-source :w w :e :d :allocation :d}]))]
        (is (nil? (m/ent final w :d)))))))

(deftest protected-registration-blocks-gc-and-generic-readiness-removes-the-blocker
  (let [actions (take 6 (protected-actions))
        before (peek (checked-walk! (m/init-state {:slices? true :cps-exit? true}) actions))
        states (checked-walk! before
                              [{:t :source-unreachable :w w :e :d :allocation :d}
                               {:t :reap-source :w w :e :d :allocation :d}
                               {:t :cleanup-deliver :n n :sequence 1 :value :external-error}
                               {:t :reap-source :w w :e :d :allocation :d}])
        waiting (nth states 1) rejected (nth states 3) final (peek states)]
    (is (= ::m/source-in-use
           (get-in (m/attempt waiting {:t :reap-source :w w :e :d :allocation :d}) [:refusal :error])))
    (is (= {} (get-in rejected [:worlds w :entities :d :deferred :protected])))
    (is (nil? (get-in rejected [:env :native n :deferred-wait])))
    (is (nil? (m/ent final w :d)))
    (is (some? (get-in final [:env :cleanup-cells cell])))
    (is (seq (inv/check (assoc-in waiting [:env :native n :deferred-wait :sequence] 99))))))

(deftest a-protected-ticket-retains-another-owners-deferred-until-resume
  (let [a [:owner 1] b [:reader 1] ticket (cleanup/ticket w b) key [w a :d]
        actions [{:t :t04 :w w :e :owner :mode :callback}
                 (assoc create :scope a)
                 {:t :t04 :w w :e :reader :mode :callback}
                 {:t :slice-enter :w w :r b :th :reader-thread}
                 {:t :finalization-wait :w w :th :reader-thread}
                 {:t :deferred-protect :w w :e :d :allocation :d :n ticket :sequence 1 :th :reader-thread}
                 {:t :t38 :th :reader-thread}
                 {:t :t11 :w w :r a}
                 (assoc (request false true) :cell key) assign-front
                 {:t :finalization-resume :w w :n ticket :th :reader-thread}
                 {:t :t07 :w w :r b :value :done}
                 {:t :t38 :th :reader-thread}]
        states (checked-walk! (m/init-state {:slices? true :cps-exit? true}) actions)
        protected (nth states 6) closed (nth states 8) ready (nth states 10)
        resumed (nth states 11)]
    (is (= #{ticket} (get-in protected [:env :cleanup-cells key :holders])))
    (is (= #{key} (get-in protected [:env :native ticket :cells])))
    (is (= {:claimed? false :protected {ticket 1}} (:deferred (m/ent protected w :d))))
    (is (nil? (m/ent closed w :d)))
    (is (= false (get-in ready [:env :native ticket :delivery])))
    (is (= :ready (get-in ready [:env :native ticket :phase])))
    (is (nil? (get-in resumed [:env :cleanup-cells key])))
    (is (nil? (get-in resumed [:env :native ticket])))))

(deftest world-release-transfers-queued-attempts-to-capability-envelopes
  (let [initial (peek (checked-walk! (m/init-state {:slices? true :cps-exit? true})
                                     (concat (take 6 (protected-actions)) [(request :ack false)])))
        released (m/step initial {:t :t34 :w w})]
    ;; Kernel's T34 remains outside its profile. Both stores independently
    ;; exercise the typed retained actions from the model's tombstone state.
    (is (empty? (inv/check released)))
    (is (empty? (inv/edge-check {:before initial :action {:t :t34 :w w} :after released})))
    (is (= :released (:status (m/wr released w))))
    (is (nil? (:queue (m/wr released w))))
    (is (= 1 (count (get-in released [:env :outside]))))
    (let [assigned (peek (checked-walk! released [assign-front]))]
      (is (= :ack (get-in assigned [:env :native n :delivery])))
      (is (empty? (get-in assigned [:env :outside]))))
    (let [empty-queue (assoc-in released [:env :outside] [])
          states (checked-walk! empty-queue [(assoc (request :second true) :cell cell) assign-front])
          queued (nth states 1) final (peek states)]
      (is (nil? (:queue (m/wr queued w))))
      (is (= 1 (count (get-in queued [:env :outside]))))
      (is (= :second (get-in final [:env :native n :delivery]))))))

(deftest retained-deferred-payload-cannot-be-mutated-through-generic-cleanup-access
  (let [initial (reduce m/step (m/init-state {:slices? true :cps-exit? true}) (protected-actions))
        ready (m/step initial {:t :cleanup-deliver :n n :sequence 1 :value :other})
        claimed (m/step ready {:t :cleanup-claim :n n :th :cleaner})
        action {:t :cleanup-cell :th :cleaner :cell cell :value :bypass}]
    (is (= ::cleanup/not-mutable-cleanup-cell (get-in (m/attempt claimed action) [:refusal :error])))
    (is (= claimed (peek (checked-walk! claimed [action]))))))

(deftest typed-assignment-readiness-needs-the-exact-receipt-and-delivered-value
  (let [before (reduce m/step (m/init-state {:slices? true :cps-exit? true})
                       (concat (take 6 (protected-actions)) [(request false false)]))
        action (assign-front before) after (m/step before action)]
    (is (empty? (inv/edge-check {:before before :action action :after after})))
    (is (seq (inv/edge-check {:before before :action (update action :seq inc) :after after})))
    (is (seq (inv/edge-check {:before before :action action
                              :after (assoc-in after [:env :native n :delivery] :counterfeit)})))))

(deftest world-release-keeps-original-attempt-order-across-queued-and-held-envelopes
  (let [initial (reduce m/step (m/init-state {:slices? true :cps-exit? true})
                        (concat (take 6 (protected-actions)) [(request :first false)]))
        first-event (first (:queue (m/wr initial w)))
        first-seq (:seq first-event)
        v [:w 1] other (m/world-row v nil :root v)
        other-before {:w v :event {:environment-marker :before}}
        other-middle {:w v :event {:environment-marker :middle}}
        other-after {:w v :event {:environment-marker :after}}
        later {:w w :event {:deferred-assignment :d :allocation :d :value :second :seq (inc first-seq)}}
        last-attempt {:w w :event {:deferred-assignment :d :allocation :d :value :third :seq (+ first-seq 2)}}
        ;; A representative fenced snapshot can contain older queued work and
        ;; newer held arrivals. Publication must preserve their original order.
        initial (-> initial (assoc-in [:worlds v] other)
                    (update :registry conj v) (update :known-worlds conj v)
                    (assoc-in [:lineages v] (:lineage other))
                    (assoc-in [:clocks w] (+ first-seq 2))
                    (assoc-in [:env :outside] [other-before later other-middle last-attempt other-after]))
        released (m/step initial {:t :t34 :w w})
        expected [other-before {:w w :event first-event} other-middle later other-after last-attempt]]
    (is (empty? (inv/check initial)))
    (is (empty? (inv/check released)))
    (is (empty? (inv/edge-check {:before initial :action {:t :t34 :w w} :after released})))
    (is (= expected (get-in released [:env :outside])))
    (let [final (peek (checked-walk! released [assign-front assign-front assign-front]))]
      (is (= :first (get-in final [:env :cleanup-cells cell :result])))
      (is (= :first (get-in final [:env :native n :delivery])))
      (is (= [other-before other-middle other-after] (get-in final [:env :outside]))))))

(deftest retired-cleanup-can-protect-an-existing-root-acknowledgement-without-starting-work
  (let [key [w [:root w] :d]
        actions [create {:t :t04 :w w :e :worker :mode :callback}
                 {:t :slice-enter :w w :r r :th :thread}
                 {:t :t11 :w w :r r}
                 {:t :cleanup-adopt :n n :th :thread}
                 {:t :cleanup-park :th :thread}
                 {:t :deferred-protect :w w :e :d :allocation :d :n n :sequence 1 :th :thread}
                 {:t :t38 :th :thread}
                 (request :ack false) assign-front
                 {:t :cleanup-claim :n n :th :cleaner}
                 {:t :cleanup-return :th :cleaner}
                 {:t :t38 :th :cleaner}]
        states (checked-walk! (m/init-state {:slices? true :cps-exit? true}) actions)
        before (nth states 6) protected (nth states 7) ready (nth states 10) final (peek states)
        forbidden {:t :deferred-create :w w :e :new :allocation :new :th :thread}]
    (is (empty? (get-in before [:env :cleanup-cells])))
    (is (= #{key} (get-in protected [:env :native n :cells])))
    (is (= #{n} (get-in protected [:env :cleanup-cells key :holders])))
    (is (nil? (m/current protected w :d)))
    (is (= :unwinding (:status (m/run protected w r))))
    (is (= ::m/cancelled (get-in (m/attempt protected forbidden) [:refusal :error])))
    (checked-walk! protected [forbidden])
    (is (= :ack (get-in ready [:env :native n :delivery])))
    (is (nil? (get-in final [:env :cleanup-cells key])))
    (is (= :ack (:result (m/ent final w :d))))))

(deftest reserved-source-and-unsupported-obligation-ingress-refuse-without-mutation
  (let [initial (peek (checked-walk! [create {:t :t04 :w w :e :worker :mode :callback}]))
        actions (concat [{:t :t02 :w w :e :reserved :kind :deferred :allocation :reserved}
                         {:t :signal-write :w w :e :d :value :bypass}
                         {:t :signal-publish :w w :e :d}]
                        (for [kind [:track :await-reactive :external :timer]]
                          {:t :t05 :w w :r r :kind kind :debtor [:entity w :d]}))]
    (doseq [action actions]
      (let [expected (case (:t action)
                       :t02 ::m/reserved-source-kind
                       :t05 ::m/unsupported-deferred-obligation
                       ::m/released)]
        (is (= expected (get-in (m/attempt initial action) [:refusal :error])))
        (is (= initial (peek (checked-walk! initial [action]))))))))

(deftest deferred-following-forks-refuse-live-sources-and-retained-capabilities
  (let [live (peek (checked-walk! [create]))
        retained (peek (checked-walk! (m/init-state {:slices? true :cps-exit? true}) (protected-actions)))
        action {:t :t19 :w w :v [:w 1] :k :fork :scope [:root w] :systems #{}}]
    (is (nil? (m/ent retained w :d)))
    (doseq [before [live retained]]
      (is (= ::m/unsupported-deferred-fork (get-in (m/attempt before action) [:refusal :error])))
      (is (= before (peek (checked-walk! before [action])))))))

(deftest deferred-cut-capture-and-restored-basis-attach-refuse-before-mutating-authority
  (let [cut {:t :t20q :c :cut :scope [:root w]
             :participants {:worlds #{w} :components #{} :systems #{}}}
        live (m/step (m/step (m/init-state) create) cut)
        captured (-> (m/init-state) (m/step cut) (m/step {:t :t22 :c :cut}))
        ;; A restored basis can predate the ingress guard. It still cannot
        ;; transplant a Deferred's protected ticket identities into a child.
        restored (assoc-in captured [:cuts :cut :basis w :entities :d]
                           (m/ent (m/step (m/init-state) create) w :d))
        cases [[live {:t :t22 :c :cut}]
               [restored {:t :t23 :c :cut :v [:w 1] :k :fork}]]]
    ;; T22/T23 remain outside the concrete kernel profile; these checks pin the
    ;; complete symbolic boundary without expanding that implementation scope.
    (doseq [[before action] cases]
      (let [{:keys [state refusal observation]} (m/attempt before action)]
        (is (= ::m/unsupported-deferred-fork (:error refusal)))
        (is (= before state))
        (is (empty? (inv/check state)))
        (is (empty? (inv/edge-check {:before before :action action :after state
                                     :refusal refusal :observation observation})))))))

(deftest generic-computation-and-keyed-row-ingress-cannot-retag-a-deferred
  (let [initial (peek (checked-walk! [create {:t :t04 :w w :e :worker :mode :callback}]))
        keyed-create {:t :deferred-create :w w :e [:worker :slot] :allocation [:worker :slot]}
        keyed (peek (checked-walk! initial [keyed-create]))
        cases [[initial {:t :t01 :w w :e :d :tok :wrong-token} ::m/not-computation]
               [initial {:t :t04 :w w :e :d :mode :callback} ::m/not-computation]
               [initial {:t :t03 :w w :r r :key :slot :kind :deferred} ::m/reserved-source-kind]
               [keyed {:t :t03 :w w :r r :key :slot :kind :cache-row} ::m/reserved-source-kind]]]
    (doseq [[before action expected] cases]
      (is (= expected (get-in (m/attempt before action) [:refusal :error])))
      (is (= before (peek (checked-walk! before [action])))))))

(deftest foreign-cold-start-envelopes-cannot-run-a-deferred-body
  (let [before (peek (checked-walk! [create]))
        envelope {:start-for :d :creditor-world w :o [:o 99] :seq 1}
        before (-> before (assoc-in [:worlds w :queue] [envelope]) (assoc-in [:clocks w] 1))
        action {:t :t37 :w w}]
    (is (= ::m/not-computation (get-in (m/attempt before action) [:refusal :error])))
    (is (= before (peek (checked-walk! before [action]))))
    (is (nil? (m/current before w :d)))))

(deftest reactive-prefix-owner-migration-keeps-all-retained-views-of-one-allocation-in-sync
  (let [owner [:owner 1] successor [:owner 2]
        b [:reader-b 1] c [:reader-c 1]
        nb (cleanup/ticket w b) nc (cleanup/ticket w c)
        old-key [w owner :d] new-key [w successor :d]
        actions [{:t :t02 :w w :e :trigger :value 0}
                 {:t :t04 :w w :e :owner :mode :callback}
                 (assoc create :scope owner :order 0)
                 {:t :t05 :w w :r owner :kind :track :debtor [:entity w :trigger] :order 1}
                 {:t :t07 :w w :r owner :value :owner}
                 {:t :t08 :w w :e :owner :value :owner}
                 {:t :t04 :w w :e :reader-b :mode :callback}
                 {:t :slice-enter :w w :r b :th :thread-b}
                 {:t :finalization-wait :w w :th :thread-b}
                 {:t :deferred-protect :w w :e :d :allocation :d :n nb :sequence 1 :th :thread-b}
                 {:t :t38 :th :thread-b}
                 {:t :signal-write :w w :e :trigger :value 1}
                 {:t :t08 :w w :e :trigger :value 1}
                 {:t :t04 :w w :e :reader-c :mode :callback}
                 {:t :slice-enter :w w :r c :th :thread-c}
                 {:t :finalization-wait :w w :th :thread-c}
                 {:t :deferred-protect :w w :e :d :allocation :d :n nc :sequence 1 :th :thread-c}
                 {:t :t38 :th :thread-c}
                 (request :ack true)
                 {:t :t11 :w w :r successor} assign-front
                 {:t :t11 :w w :r b}
                 {:t :cleanup-claim :n nb :th :cleaner-b}
                 {:t :cleanup-return :th :cleaner-b}
                 {:t :t38 :th :cleaner-b}
                 {:t :t11 :w w :r c}
                 {:t :cleanup-claim :n nc :th :cleaner-c}
                 {:t :cleanup-return :th :cleaner-c}
                 {:t :t38 :th :cleaner-c}]
        states (checked-walk! (m/init-state {:slices? true :cps-exit? true}) actions)
        migrated (nth states 13) registered (nth states 18) assigned (nth states 21)
        one-returned (nth states 25) final (peek states)]
    (is (= successor (:owner (m/ent migrated w :d))))
    (doseq [key [old-key new-key]]
      (is (= {nb 1 nc 1} (get-in registered [:env :cleanup-cells key :deferred :protected])))
      (is (= {:assigned? true :claimed? true :protected {}}
             (get-in assigned [:env :cleanup-cells key :deferred])))
      (is (= :ack (get-in assigned [:env :cleanup-cells key :result]))))
    (doseq [ticket [nb nc]]
      (is (= :ready (get-in assigned [:env :native ticket :phase])))
      (is (= :ack (get-in assigned [:env :native ticket :delivery]))))
    (is (nil? (get-in one-returned [:env :cleanup-cells old-key])))
    (is (some? (get-in one-returned [:env :cleanup-cells new-key])))
    (is (nil? (m/ent final w :d)))
    (is (empty? (get-in final [:env :cleanup-cells])))))
