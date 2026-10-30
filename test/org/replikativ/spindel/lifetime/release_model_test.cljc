(ns org.replikativ.spindel.lifetime.release-model-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [clojure.walk :as data-walk]
            [org.replikativ.spindel.engine.kernel :as kernel]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.lifetime.lifecycle :as lifecycle]
            [org.replikativ.spindel.lifetime.invariants :as inv]))

(def w [:w 0])
(def root [:root w])
(def r [:worker 1])
(def release (lifecycle/release-id w))
(def observer [release 1])
(def request {:t :release-request :w w :release release :reason :first-reason})
(def observe {:t :release-observe :w w :release release :observer observer})
(def detach {:t :release-detach :w w :release release :observer observer})
(def notify {:t :release-notify :w w :release release :observer observer})
(def exit {:t :t38 :th :engine})
(defn row [s] (get-in s [:env :releases w]))

(defn view [s]
  (let [s (data-walk/postwalk
           (fn [value]
             (if (and (keyword? value) (#{"cancelled" "released"} (name value))
                      (#{"org.replikativ.spindel.engine.kernel" "org.replikativ.spindel.lifetime.model"} (namespace value)))
               (keyword "error" (name value)) value))
           (select-keys s [:worlds :env :serial :events :clocks :registry :generation-clock]))]
    (update s :events
            #(vec (mapcat (fn [group]
                            (if (= :obligation-exit (:event (first group)))
                              (sort-by (juxt (comp pr-str :world) (comp pr-str :o)) group) group))
                          (partition-by (fn [event] (= :obligation-exit (:event event))) %))))))

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
               (is (= (view after) (view (kernel/snapshot implementation))) (pr-str action))))
           after)) initial actions)))))

(defn refuses [s action expected]
  (is (= expected (get-in (m/attempt s action) [:refusal :error])))
  (is (= s (peek (walk s [action])))))

(defn physical []
  (peek (walk [{:t :t04 :w w :e :worker :mode :deref}
               {:t :slice-enter :w w :r r :th :engine}])))

(deftest idle-release-is-immediate-repeatable-and-observers-are-external
  (let [states (walk [request (assoc request :reason :ignored) observe notify
                      (assoc observe :observer [release 2])
                      (assoc detach :observer [release 2]) (assoc detach :observer [release 2])])
        first-request (nth states 1) end (peek states)
        events (mapcat :events states)]
    (is (= {:id release :reason :first-reason :phase :joined :next-observer 0 :observers {} :result nil}
           (row first-request)))
    (is (= :first-reason (:reason (row end))))
    (is (= 1 (count (filter #(= :release-joined (:event %)) events))))
    (is (= [{:event :release-delivery :world w :release release :observer observer :variant :ok :value nil}]
           (filterv #(= :release-delivery (:event %)) events)))
    (is (= #{:id :lineage :status} (set (keys (m/wr end w)))))
    (is (empty? (:observers (row end))))
    (is (empty? (get-in end [:env :native])))
    (refuses end notify ::lifecycle/not-release-ready)))

(deftest observer-registration-and-last-physical-return-have-no-lost-wakeup
  (doseq [observer-first? [false true] reason [nil false :explicit]]
    (let [initial (physical)
          pending (peek (walk initial [(assoc request :reason reason)]))
          end (peek (walk pending (if observer-first? [observe exit notify] [exit observe notify])))]
      (is (= :releasing (:phase (row pending))))
      (is (= reason (:reason (row end))))
      (is (= :joined (:phase (row end))))
      (is (= nil (:result (row end))))
      (is (empty? (:observers (row end))))
      (is (= :release-delivery (:event (last (:events end)))))
      (is (m/join-ready? end w w)))))

(deftest timeout-and-detach-do-not-cancel-release-or-forge-a-return
  (let [pending (peek (walk (physical) [request observe detach detach]))
        timeout {:t :join :w w :x w :timeout? true}
        attempt (m/attempt pending timeout)
        joined (peek (walk pending [exit]))]
    (is (= ::m/join-timeout (get-in attempt [:refusal :error])))
    (is (= pending (:state attempt)))
    (is (= :releasing (:phase (row pending))))
    (is (= :joined (:phase (row joined))))
    (is (empty? (:observers (row joined))))
    (refuses joined notify ::lifecycle/not-release-ready)))

(deftest receipts-observers-and-self-join-evidence-are-authenticated-before-mutation
  (let [pending (peek (walk (physical) [request]))]
    (refuses pending (assoc observe :caller-th :engine) ::lifecycle/release-self-join)
    (refuses pending (assoc observe :caller-th :missing) ::lifecycle/invalid-release-caller)
    (refuses pending (assoc observe :caller-th false) ::lifecycle/invalid-release-caller)
    (doseq [evidence [{:op false} {:op :counterfeit} {:callback false}]]
      (refuses pending (merge observe evidence) ::lifecycle/invalid-release-caller))
    ;; A supplied raw callback identity meets the generic capability fence
    ;; before the lifecycle helper can authenticate observation evidence.
    (refuses pending (assoc observe :callback :counterfeit) ::m/cleanup-only)
    (refuses pending (assoc observe :frame :counterfeit) ::lifecycle/invalid-release-caller)
    (refuses pending (assoc observe :release [:world-release [:w 1]]) ::lifecycle/invalid-release-receipt)
    (refuses pending (assoc detach :observer [release 99]) ::lifecycle/not-release-observer)
    (refuses pending notify ::lifecycle/not-release-ready)
    (refuses pending (assoc request :caller-th :engine) ::m/cleanup-only)
    (let [enrolled (peek (walk pending [observe]))]
      (refuses enrolled observe ::lifecycle/not-release-observer))))

(deftest direct-t34-and-root-t13-still-use-the-original-default-release-semantics
  (doseq [action [{:t :t34 :w w} {:t :t13 :w w :scope root}]]
    (let [initial (physical) released (peek (walk initial [action]))]
      (is (nil? (row released)))
      (is (= :released (:status (m/wr released w))))
      (is (some #(and (= :host-delivery (:event %)) (= ::m/released (:value %))) (:events released)))
      (walk released [exit]))))

(deftest retained-producers-preserve-run-order-and-never-reuse-consumed-receipts
  (doseq [kind [:deferred :mailbox]
          release-action [{:t :t34 :w w} request]]
    (let [e :input cell [w r e]
          create (if (= kind :deferred) :deferred-create :mailbox-create)
          producer (if (= kind :deferred) :deferred-request :mailbox-post-request)
          envelope-key (if (= kind :deferred) :deferred-assignment :mailbox-post)
          ingress (if (= kind :deferred) :deferred-assign :mailbox-post)
          initial (peek (walk (m/init-state {:slices? true :cps-exit? true})
                              [{:t :t04 :w w :e :worker :mode :callback}
                               {:t :slice-enter :w w :r r :th :engine}
                               {:t create :w w :e e :allocation e :scope r}
                               {:t :finalization-wait :w w :th :engine} exit]))
          released (peek (walk initial [release-action release-action release-action]))
          post {:t producer :w w :e e :allocation e :cell cell :value :same-payload}]
      ;; No event has ever advanced the event clock. The run clock is the
      ;; only evidence that the next accepted producer sequence must be 2.
      (is (= 1 (:seq (m/wr initial w))))
      (is (= 0 (get-in initial [:clocks w] 0)))
      (is (empty? (:queue (m/wr initial w))))
      (is (= 1 (get-in released [:clocks w])))
      (is (= #{:id :lineage :status} (set (keys (m/wr released w)))))
      (loop [before released sequence 2 stale nil]
        (when (< sequence 5)
          (let [queued (peek (walk before [post]))
                event (get-in queued [:env :outside 0 :event])
                receipt (assoc (dissoc event envelope-key) :t ingress :w w :e e)]
            (is (= sequence (:seq event)))
            (when (= kind :mailbox)
              (is (= [e sequence] (:message-id event))))
            ;; Identical allocation, cell and payload cannot turn an old
            ;; consumed receipt into authority over a later accepted attempt.
            (when stale
              (refuses queued stale (if (= kind :deferred) ::m/not-deferred-assignment ::m/not-mailbox-post)))
            (let [consumed (peek (walk queued [receipt]))]
              (is (empty? (get-in consumed [:env :outside])))
              (is (= sequence (get-in consumed [:clocks w])))
              (recur consumed (inc sequence) receipt))))))))

(deftest release-preserves-an-event-clock-already-ahead-of-run-creation
  (let [initial (peek (walk [{:t :t04 :w w :e :worker :mode :callback}
                             {:t :deferred-create :w w :e :input :allocation :input :scope root}
                             {:t :deferred-request :w w :e :input :allocation :input :value 41}
                             (fn [s]
                               (assoc (dissoc (first (:queue (m/wr s w))) :deferred-assignment)
                                      :t :deferred-assign :w w :e :input))
                             {:t :queued :w w}]))
        released (peek (walk initial [request request {:t :t34 :w w} request]))]
    (is (= 1 (:seq (m/wr initial w))))
    (is (= 3 (get-in initial [:clocks w])))
    (is (empty? (:queue (m/wr initial w))))
    (is (= 3 (get-in released [:clocks w])))
    (is (= #{:id :lineage :status} (set (keys (m/wr released w)))))))

(deftest raw-rejection-keeps-the-first-explicit-release-reason
  (doseq [reason [nil false {:explicit :release-reason}]]
    (let [mb :mailbox consumer [:host [:o 0]]
          receipt [:mailbox-callback w root consumer] frame [:mailbox-frame consumer]
          before (peek (walk [{:t :mailbox-create :w w :e mb :allocation mb}
                              {:t :mailbox-take :w w :e mb :allocation mb :kind :host
                               :consumer consumer :o [:o 0] :order 0}]))
          released (peek (walk before [(assoc request :reason reason) (assoc request :reason :replacement) observe]))
          entered (peek (walk released [{:t :mailbox-claim :w w :e mb :allocation mb :consumer consumer
                                         :variant :error :callback receipt :frame frame}]))]
      (is (= reason (get-in released [:env :native receipt :delivery])))
      (is (= :waiting (get-in released [:env :releases w :observers observer :state])))
      (refuses entered (assoc observe :observer [release 2] :callback receipt :frame frame)
               ::lifecycle/release-self-join)
      (let [done (peek (walk entered [{:t :mailbox-return :w w :e mb :allocation mb :consumer consumer :frame frame}
                                      notify]))]
        (is (= reason (:reason (row done))))
        (is (= :joined (:phase (row done))))))))

(deftest timer-disposal-and-installer-return-remain-independent-join-obligations
  (let [o [:o 1] n [:timer w o]
        waiting (peek (walk (physical)
                            [{:t :timer-register :w w :r r :th :engine :o o :n n :order 0 :delay-ms 1 :value 41}]))
        released (peek (walk waiting [request observe]))
        disposed (peek (walk released [{:t :timer-install-result :w w :n n :variant :ok :handle? true}
                                       {:t :timer-handle-release :w w :n n :phase :claim}
                                       {:t :timer-handle-release :w w :n n :phase :returned :variant :ok}]))
        done (peek (walk disposed [exit notify]))]
    (is (= :releasing (:phase (row released))))
    (is (= :releasing (:phase (row disposed))))
    (is (empty? (get-in disposed [:env :native])))
    (is (= :joined (:phase (row done))))))

(deftest completion-oracle-rejects-logical-only-join-and-observer-loss
  (let [pending (peek (walk (physical) [request observe]))
        forged (-> pending (assoc-in [:env :releases w :phase] :joined)
                   (assoc-in [:env :releases w :result] nil)
                   (assoc-in [:env :releases w :observers observer :state] :ready))
        lost (update-in pending [:env :releases w :observers] dissoc observer)]
    (is (seq (inv/release-errors forged)))
    (is (seq (inv/release-edge-errors {:before pending :action {:t :source-unreachable :w w} :after forged})))
    (is (seq (inv/release-edge-errors {:before pending :action {:t :source-unreachable :w w} :after lost})))
    (is (seq (inv/release-edge-errors {:before pending :action {:t :release-detach :w w} :after forged})))))

(deftest unsupported-root-profiles-refuse-before-fencing-or-issuing-a-receipt
  (let [initial (m/init-state {:slices? true})
        foreign [:w 1]
        followed (m/step initial {:t :t19 :w w :v foreign :k :fork :scope root :systems #{}})
        child-request {:t :release-request :w foreign :release (lifecycle/release-id foreign) :reason :reason}
        cut (m/step initial {:t :t20 :c :cut :scope root
                             :participants {:worlds #{w} :components #{} :systems #{}}})
        remote (-> initial
                   (assoc-in [:worlds foreign] (m/world-row foreign nil :root foreign))
                   (update :registry conj foreign) (update :known-worlds conj foreign)
                   (assoc-in [:lineages foreign] (:lineage (m/world-row foreign nil :root foreign))))
        pending (-> remote
                    (m/step {:t :t04 :w w :e :worker :mode :callback})
                    (m/step {:t :t05 :w w :r r :kind :await-once :debtor [:entity foreign :remote]}))]
    (doseq [[before action] [[followed request] [followed child-request] [cut request] [pending request]]]
      (refuses before action ::m/unsupported-world-release)
      (is (= :live (:status (m/wr before (:w action)))))
      (is (nil? (get-in before [:env :releases (:w action)]))))))

(deftest release-retains-protected-input-transform-and-waits-for-actual-cleanup-return
  (let [n (cleanup/ticket w r) op [n 1] startup [op 1] reg [op 1] callback [op 2]
        cell [w r :d]
        initial (peek (walk (m/init-state {:slices? true :cps-exit? true})
                            [{:t :t04 :w w :e :worker :mode :callback}
                             {:t :slice-enter :w w :r r :th :engine}
                             {:t :deferred-create :w w :e :d :allocation :d :scope r}
                             {:t :finalization-wait :w w :th :engine}
                             {:t :operation-start :w w :n n :op op :sequence 1 :frame startup}
                             {:t :operation-await :w w :n n :op op :sequence 1 :frame startup
                              :reg reg :e :d :allocation :d :continuation reg}
                             {:t :operation-return :w w :n n :op op :sequence 1 :frame startup}
                             exit]))
        released (peek (walk initial [request observe]))
        ready (peek (walk released [{:t :deferred-request :w w :e :d :allocation :d :cell cell :value 41}
                                    (fn [s]
                                      (assoc (dissoc (get-in s [:env :outside 0 :event]) :deferred-assignment)
                                             :t :deferred-assign :w w :e :d))]))
        entered (peek (walk ready [{:t :operation-claim :w w :n n :op op :sequence 1 :reg reg :frame callback}]))]
    (is (= :first-reason (get-in released [:env :native n :cancel-value])))
    (is (= 41 (get-in ready [:env :native n :operation :registrations reg :delivery])))
    (is (= :waiting (get-in ready [:env :native n :phase])))
    (refuses entered (assoc observe :observer [release 2] :op op :frame callback)
             ::lifecycle/release-self-join)
    (refuses entered (assoc observe :observer [release 2] :op op :frame [op 99])
             ::lifecycle/invalid-release-caller)
    (let [terminal (peek (walk entered [{:t :operation-terminal :w w :n n :op op :sequence 1
                                         :variant :ok :value 42}]))
          done (peek (walk terminal [{:t :operation-return :w w :n n :op op :sequence 1 :reg reg :frame callback}
                                     {:t :cleanup-claim :n n :th :cleaner}
                                     {:t :cleanup-return :th :cleaner}
                                     {:t :t38 :th :cleaner} notify]))]
      (is (= 42 (get-in terminal [:env :native n :delivery])))
      (is (= :releasing (:phase (row terminal))))
      (is (= :joined (:phase (row done))))
      (is (nil? (:runs (m/wr done w))))
      (is (empty? (get-in done [:env :cleanup-cells]))))))

(deftest releasing-the-target-keeps-an-independent-world-and-idle-selection-live
  (let [foreign [:w 1]
        initial (-> (m/init-state {:slices? true})
                    (assoc-in [:worlds foreign] (m/world-row foreign nil :root foreign))
                    (update :registry conj foreign) (update :known-worlds conj foreign)
                    (assoc-in [:lineages foreign] (:lineage (m/world-row foreign nil :root foreign))))
        initial (peek (walk initial [{:t :t04 :w foreign :e :foreign-worker :mode :deref}
                                     {:t :slice-enter :w foreign :r [:foreign-worker 1] :th :foreign}]))
        released (peek (walk initial [request (assoc observe :caller-th :foreign) notify]))]
    (is (= :joined (:phase (row released))))
    (is (= :live (:status (m/wr released foreign))))
    (is (= :running (:status (m/run released foreign [:foreign-worker 1]))))
    (is (= [:foreign-worker 1] (get-in released [:env :threads :foreign :run])))))

(deftest joined-release-drops-only-dead-accepted-input-before-observer-delivery
  (doseq [kind [:deferred :mailbox]]
    (let [n (cleanup/ticket w r) op [n 1] startup [op 1] reg [op 1] callback [op 2]
          e :input cell [w r e]
          create (if (= kind :deferred) :deferred-create :mailbox-create)
          producer (if (= kind :deferred) :deferred-request :mailbox-post-request)
          envelope-key (if (= kind :deferred) :deferred-assignment :mailbox-post)
          ingress (if (= kind :deferred) :deferred-assign :mailbox-post)
          initial (peek (walk (m/init-state {:slices? true :cps-exit? true})
                              [{:t :t04 :w w :e :worker :mode :callback}
                               {:t :slice-enter :w w :r r :th :engine}
                               {:t create :w w :e e :allocation e :scope r}
                               {:t :finalization-wait :w w :th :engine}
                               {:t :operation-start :w w :n n :op op :sequence 1 :frame startup}
                               {:t :operation-await :w w :n n :op op :sequence 1 :frame startup
                                :reg reg :e e :allocation e :continuation reg}
                               {:t :operation-return :w w :n n :op op :sequence 1 :frame startup} exit
                               request observe]))
          queued (peek (walk initial [{:t producer :w w :e e :allocation e :cell cell :value 41}
                                      {:t producer :w w :e e :allocation e :cell cell
                                       :value {:unobserved :large-payload}}]))
          ready (peek (walk queued [(fn [s]
                                      (assoc (dissoc (get-in s [:env :outside 0 :event]) envelope-key)
                                             :t ingress :w w :e e))]))
          stale (first (get-in ready [:env :outside]))
          foreign {:w [:w 99] :event {:deferred-assignment :foreign-input :allocation :foreign-input
                                      :seq 1 :value :foreign-payload}}
          committed {:w w :event {:committed-notification :already-won :value :notification-payload}}
          ready (update-in ready [:env :outside] into [committed foreign])
          actions [{:t :operation-claim :w w :n n :op op :sequence 1 :reg reg :frame callback}
                   {:t :operation-terminal :w w :n n :op op :sequence 1 :variant :ok :value 42}
                   {:t :operation-return :w w :n n :op op :sequence 1 :reg reg :frame callback}
                   {:t :cleanup-claim :n n :th :cleaner}
                   {:t :cleanup-return :th :cleaner}
                   {:t :t38 :th :cleaner}]
          states (walk ready actions) before-return (nth states 5) joined (peek states)
          corrupt (update-in joined [:env :outside] #(into [stale] %))]
      ;; Both attempts remain authenticated while cleanup owns the allocation.
      (is (= 2 (count (get-in queued [:env :outside]))))
      (is (= {:unobserved :large-payload} (get-in stale [:event :value])))
      (is (= :releasing (:phase (row before-return))))
      (is (= stale (first (get-in before-return [:env :outside]))))
      ;; Join publication, not an observer's eventual return, releases the
      ;; second payload. Committed notifications and other worlds survive.
      (is (= :joined (:phase (row joined))))
      (is (= :ready (get-in joined [:env :releases w :observers observer :state])))
      (is (= [committed foreign] (get-in joined [:env :outside])))
      (is (seq (inv/release-errors corrupt)))
      (is (seq (inv/release-edge-errors {:before before-return :action (last actions) :after corrupt})))
      (is (seq (inv/release-edge-errors
                {:before before-return :action (last actions)
                 :after (update-in joined [:env :outside] #(vec (remove #{committed} %)))}))))))
