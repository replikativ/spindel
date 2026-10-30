(ns org.replikativ.spindel.lifetime.mailbox-model-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [clojure.walk :as data-walk]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.engine.kernel :as kernel]))

(def w [:w 0])
(def r [:worker 1])
(def n (cleanup/ticket w r))
(def op [n 1])
(def startup [op 1])
(def reg [op 1])
(def mb :mailbox)
(def create {:t :mailbox-create :w w :e mb :allocation mb})
(def host1 [:host [:o 0]])
(def host2 [:host [:o 1]])
(def ordinary1 [:obligation [:o 1]])
(defn control [s] (cleanup/mailbox-control s w mb mb))
(defn request [value] {:t :mailbox-post-request :w w :e mb :allocation mb :value value})
(defn front [s]
  (let [event (or (first (:queue (m/wr s w)))
                  (:event (first (filter #(= w (:w %)) (get-in s [:env :outside])))))]
    (assoc (dissoc event :mailbox-post) :t :mailbox-post :w w :e (:mailbox-post event))))
(defn host-take [o] {:t :mailbox-take :w w :e mb :allocation mb :kind :host
                     :consumer [:host o] :o o :order 0})
(defn claim [s consumer & [inline? th]]
  {:t :mailbox-claim :w w :e mb :allocation mb :consumer consumer
   :message-id (get-in (control s) [:reservations consumer :message-id])
   :frame [:mailbox-frame consumer] :inline? (boolean inline?) :th th})
(defn returned [consumer] {:t :mailbox-return :w w :e mb :allocation mb :consumer consumer
                           :frame [:mailbox-frame consumer]})
(defn operation-action [t fields]
  (merge {:t t :w w :n n :op op :sequence 1} fields))

(defn snapshot-view [state]
  (let [state (data-walk/postwalk
               (fn [value]
                 (if (and (keyword? value) (#{"cancelled" "released"} (name value))
                          (#{"org.replikativ.spindel.engine.kernel" "org.replikativ.spindel.lifetime.model"} (namespace value)))
                   (keyword "error" (name value)) value))
               (select-keys state [:worlds :env :serial :events :clocks :registry :generation-clock]))]
    ;; Obligation removal diagnostics follow private map iteration. Preserve
    ;; the exact position/order of all delivery and Mailbox observations.
    (update state :events
            #(vec (mapcat (fn [group]
                            (if (= :obligation-exit (:event (first group)))
                              (sort-by (juxt (comp pr-str :world) (comp pr-str :o)) group)
                              group))
                          (partition-by (fn [event] (= :obligation-exit (:event event))) %))))))

(defn walk
  ([actions] (walk (m/init-state {:slices? true :cps-exit? true}) actions))
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
               (is (= (snapshot-view after) (snapshot-view (kernel/snapshot implementation)))
                   (pr-str action))))
           after)) initial actions)))))

(deftest posts-are-fifo-and-values-do-not-select-error-disposition
  (let [values [nil false {:external-error :data} 41]
        initial (peek (walk [create]))
        filled (peek (walk initial (mapcat (fn [value] [(request value) front]) values)))]
    (is (= values (mapv :value (:messages (control filled)))))
    (let [actions (mapcat (fn [index]
                            [(host-take [:o index]) #(claim % [:host [:o index]] true)
                             (returned [:host [:o index]])]) (range (count values)))
          states (walk filled actions)
          entries (mapcat #(filter (fn [event] (= :mailbox-entry (:event event))) (:events %)) states)]
      (is (= values (mapv :value entries)))
      (is (every? #(= :ok (:variant %)) entries))
      (is (empty? (:messages (control (peek states)))))
      (is (empty? (:reservations (control (peek states)))))
      (is (empty? (get-in (peek states) [:env :native]))))))

(deftest mixed-pending-consumers-share-one-fifo-and-an-ordinary-reservation-stays-cancellable
  (let [actions [create (host-take [:o 0])
                 {:t :t04 :w w :e :worker :mode :callback}
                 {:t :mailbox-take :w w :e mb :allocation mb :consumer [:obligation [:o 2]]
                  :kind :ordinary :o [:o 2] :r r :order 0}
                 (host-take [:o 3])
                 (request :first) front (request :second) front (request :third) front]
        states (walk actions) selected (peek states)]
    (is (= :first (get-in (control selected) [:reservations host1 :value])))
    (is (= :second (get-in (control selected) [:reservations [:obligation [:o 2]] :value])))
    (is (= :third (get-in (control selected) [:reservations [:host [:o 3]] :value])))
    (is (= :armed (get-in selected [:worlds w :obligations [:o 2] :slot])))
    (let [cancelled (peek (walk selected [{:t :t11 :w w :r r}]))
          reposted (peek (walk cancelled [front]))]
      (is (= :second (:value (last (:messages (control reposted))))))
      (is (nil? (get-in (control reposted) [:reservations [:obligation [:o 2]]]))))))

(deftest cancellation-before-selection-does-not-consume-a-message
  (let [states (walk [create {:t :t04 :w w :e :worker :mode :callback}
                      {:t :mailbox-take :w w :e mb :allocation mb :consumer ordinary1
                       :kind :ordinary :o [:o 1] :r r :order 0}
                      {:t :t11 :w w :r r} (request :saved) front])
        final (peek states)]
    (is (= [:saved] (mapv :value (:messages (control final)))))
    (is (empty? (:consumers (control final))))))

(deftest selected-reservation-cancellation-returns-to-tail-once
  (let [selected (peek (walk [create (host-take [:o 0]) (request :first) front
                              (request :second) front]))
        detached (peek (walk selected [{:t :mailbox-detach :w w :e mb :allocation mb :consumer host1}]))
        final (peek (walk detached [front]))]
    (is (= [:second :first] (mapv :value (:messages (control final)))))
    (is (= 2 (count (set (map :id (:messages (control final)))))))
    (is (= ::m/not-mailbox-consumer
           (get-in (m/attempt final {:t :mailbox-detach :w w :e mb :allocation mb :consumer host1}) [:refusal :error])))))

(deftest raw-frame-joins-its-real-owner-and-retains-only-the-named-allocation
  (let [owner [:owner 1]
        initial (peek (walk [{:t :t04 :w w :e :owner :mode :callback}
                             (assoc create :scope owner)
                             {:t :t02 :w w :scope owner :e :neighbor :kind :atom :value :secret}
                             (host-take [:o 1]) (request 41) front #(claim % host2)]))
        receipt [:mailbox-callback w owner host2]
        retired (peek (walk initial [{:t :t11 :w w :r owner}]))
        callback {:callback receipt :frame [:mailbox-frame host2]}
        forbidden (merge {:t :cleanup-cell :w w :cell [w owner :neighbor]} callback)]
    (is (false? (m/join-ready? retired w owner)))
    (is (= #{[w owner mb]} (get-in retired [:env :native receipt :cells])))
    (is (nil? (get-in retired [:env :cleanup-cells [w owner :neighbor]])))
    (is (= ::cleanup/missing-cleanup-cell (get-in (m/attempt retired forbidden) [:refusal :error])))
    (let [posted (peek (walk retired [(merge (request :ack) callback {:cell [w owner mb]}) front
                                      (returned host2)]))]
      (is (m/join-ready? posted w owner))
      (is (empty? (get-in posted [:env :cleanup-cells])))
      (is (nil? (m/ent posted w mb))))))

(defn operation-setup []
  [create {:t :t04 :w w :e :worker :mode :callback}
   {:t :slice-enter :w w :r r :th :worker}
   {:t :finalization-wait :w w :th :worker}
   (operation-action :operation-start {:frame startup})
   (operation-action :operation-await {:e mb :allocation mb :reg reg :frame startup :continuation reg})
   (operation-action :operation-return {:frame startup})])

(deftest message-readiness-enters-the-supplied-transform-before-terminal
  (let [states (walk (concat (operation-setup) [(request 41) front]))
        ready (peek states)
        input (get-in ready [:env :native n :operation :registrations reg :delivery])
        entered (peek (walk ready [(operation-action :operation-claim {:reg reg :frame [op 2]})]))
        event (last (:events entered))
        terminal (peek (walk entered [(operation-action :operation-terminal {:value (inc input) :variant :ok})
                                      (operation-action :operation-return {:reg reg :frame [op 2]})]))]
    (is (= :waiting (get-in ready [:env :native n :phase])))
    (is (= 41 input (:value event)))
    (is (= :continuation-entry (:event event)))
    (is (= reg (:continuation event)))
    (is (= 42 (get-in terminal [:env :native n :delivery])))
    (is (empty? (:reservations (control terminal))))))

(deftest terminal-returns-unclaimed-operation-reservations
  (let [ready (peek (walk (concat (operation-setup) [(request 41) front])))
        terminal (peek (walk ready [(operation-action :operation-terminal {:value :other :variant :ok}) front]))]
    (is (= [41] (mapv :value (:messages (control terminal)))))
    (is (empty? (get-in terminal [:env :native n :operation :registrations])))
    (is (= :other (get-in terminal [:env :native n :delivery])))))

(deftest queued-inline-operation-input-is-claimed-and-survives-parent-cancellation
  (let [initial (peek (walk [create (request 41) front {:t :t04 :w w :e :worker :mode :callback}
                             {:t :slice-enter :w w :r r :th :worker}
                             {:t :finalization-wait :w w :th :worker}
                             (operation-action :operation-start {:frame startup})
                             (operation-action :operation-await {:e mb :allocation mb :reg reg :frame startup :continuation reg})]))
        retired (peek (walk initial [{:t :t11 :w w :r r}]))
        final (peek (walk retired [(operation-action :operation-terminal {:variant :ok :value :first})
                                   (operation-action :operation-claim {:reg reg :frame startup :inline? true})
                                   (operation-action :operation-return {:reg reg :frame startup :inline? true})
                                   (operation-action :operation-return {:frame startup})]))]
    (is (empty? (:messages (control final))))
    (is (empty? (:reservations (control final))))
    (is (= :first (get-in final [:env :native n :delivery])))))

(deftest ordinary-inline-claim-survives-cancellation-on-the-exact-existing-frame
  (let [before (peek (walk [create (request 41) front {:t :t04 :w w :e :worker :mode :callback}
                            {:t :slice-enter :w w :r r :th :worker}
                            {:t :mailbox-take :w w :e mb :allocation mb :consumer ordinary1
                             :kind :ordinary :o [:o 1] :r r :order 0 :th :worker}]))
        retired (peek (walk before [{:t :t11 :w w :r r}]))
        entered (peek (walk retired [#(claim % ordinary1 true :worker)]))]
    (is (= :unwinding (:status (m/run entered w r))))
    (is (= 41 (:value (last (:events entered)))))
    (is (empty? (:messages (control entered))))
    (is (= ::m/not-mailbox-reservation
           (get-in (m/attempt entered (claim entered ordinary1 true :worker)) [:refusal :error])))))

(deftest expired-raw-capability-cannot-construct-root-work
  (let [receipt [:mailbox-callback w [:root w] host1]
        before (m/init-state)
        action {:t :t02 :w w :e :forged :value 41 :callback receipt :frame [:mailbox-frame host1]}]
    (is (= ::m/cleanup-only (get-in (m/attempt before action) [:refusal :error])))
    (is (= before (:state (m/attempt before action))))))

(deftest garbage-collection-may-dispose-an-unobservable-buffer-but-not-a-live-reservation
  (let [buffered (peek (walk [create (request :discardable) front
                              {:t :source-unreachable :w w :e mb :allocation mb}]))
        disposed (peek (walk buffered [{:t :reap-source :w w :e mb :allocation mb}]))
        pending (peek (walk [create (host-take [:o 0])
                             {:t :source-unreachable :w w :e mb :allocation mb}]))]
    (is (nil? (m/ent disposed w mb)))
    (is (= ::m/source-in-use
           (get-in (m/attempt pending {:t :reap-source :w w :e mb :allocation mb}) [:refusal :error])))))

(deftest ordinary-source-retirement-rejects-pending-and-selected-consumers-without-consuming
  (doseq [selected? [false true]]
    (let [owner [:owner 1]
          initial (peek (walk (concat
                               [{:t :t04 :w w :e :owner :mode :callback} (assoc create :scope owner)
                                {:t :t04 :w w :e :worker :mode :callback}
                                {:t :mailbox-take :w w :e mb :allocation mb :consumer [:obligation [:o 2]]
                                 :kind :ordinary :o [:o 2] :r r :order 0}]
                               (when selected? [(request 41) front]))))
          states (walk initial [{:t :t11 :w w :r owner}])
          retired (peek states)]
      (is (= :running (:status (m/run retired w r))))
      (is (nil? (get-in retired [:worlds w :obligations [:o 2]])))
      (is (some #(and (= :resume (:event %)) (= [:o 2] (:o %))) (:events retired))))))

(deftest queued-raw-rejection-is-a-join-participant-before-its-physical-frame
  (let [owner [:owner 1] consumer [:host [:o 1]]
        before (peek (walk [{:t :t04 :w w :e :owner :mode :callback} (assoc create :scope owner)
                            (host-take [:o 1])]))
        retired (peek (walk before [{:t :t11 :w w :r owner}]))
        receipt [:mailbox-callback w owner consumer]
        claim-error {:t :mailbox-claim :w w :e mb :allocation mb :consumer consumer :variant :error
                     :callback receipt :frame [:mailbox-frame consumer]}
        entered (peek (walk retired [claim-error]))
        final (peek (walk entered [(returned consumer)]))]
    (is (= :queued (get-in retired [:env :native receipt :phase])))
    (is (false? (get-in retired [:env :native receipt :physical?])))
    (is (nil? (get-in retired [:env :native receipt :frame])))
    (is (empty? (:physical (control retired))))
    (is (false? (m/join-ready? retired w owner)))
    (is (= :org.replikativ.spindel.engine.protocols/cancelled
           (get-in retired [:env :native receipt :delivery])))
    (is (= :mailbox-rejection-entry (:event (last (:events entered)))))
    (is (m/join-ready? final w owner))))

(deftest mailbox-generic-ingress-cannot-forge-delivery-or-source-completion
  (let [before (peek (walk [create {:t :t04 :w w :e :worker :mode :callback}
                            {:t :mailbox-take :w w :e mb :allocation mb :consumer ordinary1
                             :kind :ordinary :o [:o 1] :r r :order 0}]))
        cases [[{:t :t06 :w w :o [:o 1] :value :forged} ::m/unsupported-mailbox-resume]
               [{:t :t08 :w w :e mb :value :broadcast} ::m/unsupported-mailbox-publication]
               [{:t :t05 :w w :r r :kind :await-once :debtor [:entity w mb]} ::m/not-running]]]
    (doseq [[action error] cases]
      (is (= error (get-in (m/attempt before action) [:refusal :error])))
      (is (= before (peek (walk before [action])))))))

(deftest raw-named-capability-cannot-park-an-unrelated-ordinary-run
  (let [before (peek (walk [create (host-take [:o 0]) (request 41) front #(claim % host1)
                            {:t :t04 :w w :e :worker :mode :callback}]))
        receipt [:mailbox-callback w [:root w] host1]
        o [:o 2]
        action {:t :mailbox-take :w w :e mb :allocation mb :consumer [:obligation o]
                :kind :ordinary :o o :r r :order 0 :callback receipt :frame [:mailbox-frame host1]}]
    (is (= ::m/not-mailbox-consumer (get-in (m/attempt before action) [:refusal :error])))
    (is (= before (peek (walk before [action]))))))

(deftest opt-in-mailbox-alphabet-has-bounded-fresh-ingress
  (let [initial (m/init-state {:mailbox? true :mailboxes 1 :mailbox-posts 1 :mailbox-takes 1 :mailbox-now 1
                               :worlds 1 :world-ids 1 :spins 0 :slices? true})
        source-action (first (filter #(= :mailbox-create (:t %)) (m/mailbox-enabled initial)))
        source (m/step initial source-action)
        post (first (filter #(= :mailbox-post-request (:t %)) (m/mailbox-enabled source)))
        posted (m/step source post)]
    (is (= :mailbox-create (:t source-action)))
    (is (not-any? #(= :mailbox-post-request (:t %)) (m/mailbox-enabled posted)))
    (is (every? map? (m/mailbox-enabled posted)))))

(deftest an-inline-physical-receipt-cannot-return-before-continuation-entry
  (let [before (peek (walk [create (request 41) front (host-take [:o 0])]))
        premature (returned host1)
        invalid-variant (assoc (claim before host1 true) :variant :unknown)]
    (is (= ::m/not-mailbox-frame (get-in (m/attempt before premature) [:refusal :error])))
    (is (= before (peek (walk before [premature invalid-variant]))))
    (is (= ::m/invalid-mailbox-variant (get-in (m/attempt before invalid-variant) [:refusal :error])))))

(deftest immediate-take-requires-the-exact-provided-message-witness
  (let [before (peek (walk [create (request 41) front]))
        action {:t :mailbox-take-now :w w :e mb :allocation mb :available? true :message-id [mb :forged]}]
    (is (= ::m/mailbox-message-mismatch (get-in (m/attempt before action) [:refusal :error])))
    (is (= before (peek (walk before [action]))))))

(deftest pending-consumer-seats-the-owner-at-first-physical-claim-after-prefix-adoption
  (let [owner [:owner 1] successor [:owner 2] consumer [:host [:o 1]]
        before (peek (walk [{:t :t04 :w w :e :owner :mode :callback}
                            (assoc create :scope owner :order 0) (host-take [:o 1])
                            {:t :t09 :w w :e :owner :cause :track :order 1}
                            (request 41) front #(claim % consumer)]))
        receipt [:mailbox-callback w successor consumer]
        retired (peek (walk before [{:t :t11 :w w :r successor}]))
        action {:t :mailbox-take :w w :e mb :allocation mb :consumer [:host [:o 2]] :kind :host
                :o [:o 2] :order 0 :cell [w successor mb]
                :callback receipt :frame [:mailbox-frame consumer]}]
    (is (= successor (:owner (m/ent before w mb))))
    (is (some? (get-in before [:env :native receipt])))
    (is (= [w successor] (get-in before [:env :native receipt :owner])))
    (is (= [w successor] (get-in retired [:env :native receipt :owner])))
    (is (true? (get-in retired [:env :native receipt :retired?])))
    (is (= ::m/cleanup-only (get-in (m/attempt retired action) [:refusal :error])))
    (is (= retired (peek (walk retired [action]))))))

(deftest inline-claimed-receipt-keeps-its-original-anchor-when-allocation-owner-migrates
  (let [owner [:owner 1] successor [:owner 2] consumer [:host [:o 1]]
        before (peek (walk [{:t :t04 :w w :e :owner :mode :callback}
                            (assoc create :scope owner :order 0) (request 41) front (host-take [:o 1])]))
        receipt [:mailbox-callback w owner consumer]
        migrated (peek (walk before [{:t :t09 :w w :e :owner :cause :track :order 1}
                                     {:t :t11 :w w :r successor}]))
        entered (peek (walk migrated [#(claim % consumer true)]))]
    (is (= [w owner] (get-in migrated [:env :native receipt :owner])))
    (is (= (get-in before [:env :native receipt :anchor]) (get-in migrated [:env :native receipt :anchor])))
    (is (true? (get-in migrated [:env :native receipt :retired?])))
    (is (= 41 (:value (last (:events entered)))))))

(deftest accepted-post-survives-the-disappearance-of-its-original-retained-owner-key
  (let [owner [:owner 1] successor [:owner 2]
        first-consumer [:host [:o 1]] second-consumer [:host [:o 2]]
        old-key [w owner mb] new-key [w successor mb]
        retired (peek (walk [{:t :t04 :w w :e :owner :mode :callback}
                             (assoc create :scope owner :order 0)
                             (request 41) front (host-take [:o 1])
                             {:t :t09 :w w :e :owner :cause :track :order 1}
                             (request 42) front (host-take [:o 2])
                             {:t :t11 :w w :r successor}
                             #(claim % first-consumer true)]))
        posted (peek (walk retired [(assoc (request 43) :cell old-key) (returned first-consumer)]))
        delivered (peek (walk posted [front]))]
    (is (nil? (get-in posted [:env :cleanup-cells old-key])))
    (is (some? (get-in posted [:env :cleanup-cells new-key])))
    (is (= old-key (:cell (first (:queue (m/wr posted w))))))
    (is (= [43] (mapv :value (:messages (control delivered)))))
    (is (= 42 (get-in (control delivered) [:reservations second-consumer :value])))))

(deftest a-preseated-inline-receipt-is-not-callback-payload-authority-before-entry
  (let [before (peek (walk [create (request 41) front (host-take [:o 0])]))
        receipt [:mailbox-callback w [:root w] host1]
        authority {:callback receipt :frame [:mailbox-frame host1] :cell [w [:root w] mb]}
        post (merge (request 99) authority)
        take-now (merge {:t :mailbox-take-now :w w :e mb :allocation mb :available? false} authority)]
    (doseq [action [post take-now]]
      (is (= ::m/cleanup-only (get-in (m/attempt before action) [:refusal :error])))
      (is (= before (peek (walk before [action])))))
    (let [entered (peek (walk before [#(claim % host1 true)]))
          accepted (peek (walk entered [take-now post]))]
      (is (nil? (:refusal (m/attempt entered take-now))))
      (is (= 99 (:value (first (:queue (m/wr accepted w)))))))))

(deftest live-raw-forwarding-authenticates-entry-at-origin-and-keeps-the-target-live
  (let [target :forwarded-mailbox
        before (peek (walk [create {:t :mailbox-create :w w :e target :allocation target}
                            (request 41) front (host-take [:o 0])]))
        receipt [:mailbox-callback w [:root w] host1]
        authority {:callback receipt :frame [:mailbox-frame host1]}
        post (merge {:t :mailbox-post-request :w w :e target :allocation target :value 42} authority)
        poll (merge {:t :mailbox-take-now :w w :e target :allocation target :available? true} authority)]
    (is (= ::m/cleanup-only (get-in (m/attempt before post) [:refusal :error])))
    (is (= ::m/cleanup-only (get-in (m/attempt before poll) [:refusal :error])))
    (let [entered (peek (walk before [#(claim % host1 true)]))
          forwarded (peek (walk entered [post front poll]))]
      (is (= 42 (:value (last (:events forwarded)))))
      (is (= #{[w [:root w] mb]} (get-in forwarded [:env :native receipt :cells])))
      (is (empty? (:physical (cleanup/mailbox-control forwarded w target target)))))))

(deftest a-live-raw-callback-can-register-a-host-consumer-owned-by-another-live-mailbox
  (let [target :forwarded-mailbox
        origin (peek (walk [create {:t :mailbox-create :w w :e target :allocation target}
                            (request 41) front (host-take [:o 0]) #(claim % host1 true)]))
        receipt [:mailbox-callback w [:root w] host1]
        consumer [:host [:o 1]]
        take-target {:t :mailbox-take :w w :e target :allocation target :kind :host :o [:o 1] :order 0
                     :consumer consumer :callback receipt :frame [:mailbox-frame host1]}
        armed (peek (walk origin [take-target (returned host1)]))
        selected (peek (walk armed [{:t :mailbox-post-request :w w :e target :allocation target :value 42} front]))
        message-id (get-in (cleanup/mailbox-control selected w target target) [:reservations consumer :message-id])
        entered (peek (walk selected [{:t :mailbox-claim :w w :e target :allocation target :consumer consumer
                                       :message-id message-id :frame [:mailbox-frame consumer]}]))
        target-receipt [:mailbox-callback w [:root w] consumer]
        input (:value (last (:events entered)))]
    (is (nil? (get-in armed [:env :native receipt])))
    (is (= [consumer] (:consumers (cleanup/mailbox-control armed w target target))))
    (is (= #{[w [:root w] target]} (get-in entered [:env :native target-receipt :cells])))
    (is (= target (get-in entered [:env :native target-receipt :allocation])))
    (is (= 42 input))
    (is (= 43 (inc input)))))

(deftest retirement-does-not-grant-the-origin-callback-other-live-mailbox-rights
  (let [owner [:owner 1] target :forwarded-mailbox consumer [:host [:o 1]]
        before (peek (walk [{:t :t04 :w w :e :owner :mode :callback} (assoc create :scope owner)
                            {:t :mailbox-create :w w :e target :allocation target}
                            (request 41) front (host-take [:o 1]) #(claim % consumer true)
                            {:t :t11 :w w :r owner}]))
        receipt [:mailbox-callback w owner consumer]
        authority {:callback receipt :frame [:mailbox-frame consumer]}
        post (merge {:t :mailbox-post-request :w w :e target :allocation target :value 42} authority)
        poll (merge {:t :mailbox-take-now :w w :e target :allocation target :available? false} authority)]
    (is (true? (get-in before [:env :native receipt :retired?])))
    (doseq [action [post poll]]
      (is (= ::m/released-mailbox (get-in (m/attempt before action) [:refusal :error])))
      (is (= before (peek (walk before [action])))))))
