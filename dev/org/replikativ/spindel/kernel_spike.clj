(ns org.replikativ.spindel.kernel-spike
  "Experimental one-world B1/B2 transition kernel, for REPL iteration.
   Load with (load-file \"dev/org/replikativ/spindel/kernel_spike.clj\"), then
   call verify! and measure!. Its projection covers selected B1/B2 fields;
   this is not a complete implementation or acceptance gate."
  (:require [org.replikativ.spindel.lifetime.model :as model])
  (:import [com.sun.management ThreadMXBean]
           [java.lang.management ManagementFactory]))

(def world-id [:w 0])
(def root-id [:root world-id])

(defn new-world []
  (atom {:scopes {root-id {:kind :world-root :parent nil :status :open}}
         :entities {} :runs {} :obligations {}
         :by-creditor {} :by-debtor {} :next-obligation 0}))

(defn snapshot-copy [world]
  (atom @world))

(defn- add-obligation! [obligations by-creditor by-debtor id ob]
  (assoc! obligations id ob)
  (assoc! by-creditor (:creditor ob)
          (conj (get by-creditor (:creditor ob) #{}) id))
  (assoc! by-debtor (:debtor ob)
          (conj (get by-debtor (:debtor ob) #{}) id)))

(defn- remove-obligation! [obligations by-creditor by-debtor id]
  (when-let [ob (get obligations id)]
    (dissoc! obligations id)
    (doseq [[index k] [[by-creditor (:creditor ob)] [by-debtor (:debtor ob)]]]
      (let [remaining (disj (get index k) id)]
        (if (seq remaining)
          (assoc! index k remaining)
          (dissoc! index k))))))

(defn transition-transient!
  "One atom publication per model action, staging every table transiently."
  [world action]
  (swap! world
         (fn [state]
           (let [entities (transient (:entities state))
                 scopes (transient (:scopes state))
                 runs (transient (:runs state))
                 obligations (transient (:obligations state))
                 by-creditor (transient (:by-creditor state))
                 by-debtor (transient (:by-debtor state))
                 next-id (:next-obligation state)
                 next-id
                 (case (:t action)
                   :t02
                   (do (assoc! entities (:e action)
                               {:kind :signal :owner (get action :scope root-id)
                                :completed? false})
                       next-id)

                   :t12
                   (do (assoc! scopes (:scope action)
                               {:kind (get action :kind :explicit)
                                :parent (:parent action) :status :open})
                       next-id)

                   :t04
                   (let [e (:e action)
                         r [e 1]
                         o [:o next-id]
                         owner (get action :scope root-id)
                         mode (get action :mode :deref)
                         ob {:kind mode :debtor [:entity world-id e]
                             :creditor [:host :caller]
                             :standing? (= mode :callback) :slot :armed}]
                     (assoc! entities e {:kind :spin :owner owner :completed? false})
                     (assoc! runs r {:spin e :owner owner :status :running})
                     (add-obligation! obligations by-creditor by-debtor o ob)
                     (inc next-id))

                   :t05
                   (let [r (:r action)
                         o [:o next-id]
                         kind (:kind action)
                         ob {:kind kind :debtor (:debtor action)
                             :creditor [:run world-id r]
                             :standing? (contains? #{:track :await-reactive} kind)
                             :slot (if (= kind :track) :consumed :armed)}]
                     (assoc! runs r (assoc (get runs r) :status
                                           (if (= kind :track) :running :parked)))
                     (add-obligation! obligations by-creditor by-debtor o ob)
                     (inc next-id))

                   :t06
                   (let [o (:o action)
                         ob (get obligations o)
                         r (nth (:creditor ob) 2)]
                     (if (:standing? ob)
                       (assoc! obligations o (assoc ob :slot :consumed))
                       (remove-obligation! obligations by-creditor by-debtor o))
                     (assoc! runs r (assoc (get runs r) :status :running))
                     next-id)

                   (throw (ex-info "Unsupported transition" {:action action})))]
             (assoc state
                    :scopes (persistent! scopes)
                    :entities (persistent! entities)
                    :runs (persistent! runs)
                    :obligations (persistent! obligations)
                    :by-creditor (persistent! by-creditor)
                    :by-debtor (persistent! by-debtor)
                    :next-obligation next-id)))))

(defn- add-obligation [state id ob]
  (-> state
      (assoc-in [:obligations id] ob)
      (update-in [:by-creditor (:creditor ob)] (fnil conj #{}) id)
      (update-in [:by-debtor (:debtor ob)] (fnil conj #{}) id)))

(defn- remove-obligation [state id]
  (let [ob (get-in state [:obligations id])
        creditor (:creditor ob)
        debtor (:debtor ob)
        remove-id (fn [index key]
                    (let [remaining (disj (get index key) id)]
                      (if (seq remaining)
                        (assoc index key remaining)
                        (dissoc index key))))]
    (-> state
        (update :obligations dissoc id)
        (update :by-creditor remove-id creditor)
        (update :by-debtor remove-id debtor))))

(defn transition!
  "Publish one small B1/B2 action. A fork sees the immutable state before or
   after this swap, never a partially updated obligation/index pair."
  [world action]
  (swap! world
         (fn [state]
           (case (:t action)
             :t02
             (assoc-in state [:entities (:e action)]
                       {:kind :signal :owner (get action :scope root-id)
                        :completed? false})

             :t12
             (assoc-in state [:scopes (:scope action)]
                       {:kind (get action :kind :explicit)
                        :parent (:parent action) :status :open})

             :t04
             (let [e (:e action)
                   mode (get action :mode :deref)
                   owner (get action :scope root-id)
                   id [:o (:next-obligation state)]
                   ob {:kind mode :debtor [:entity world-id e]
                       :creditor [:host :caller]
                       :standing? (= mode :callback) :slot :armed}]
               (-> state
                   (assoc-in [:entities e]
                             {:kind :spin :owner owner :completed? false})
                   (assoc-in [:runs [e 1]]
                             {:spin e :owner owner :status :running})
                   (add-obligation id ob)
                   (update :next-obligation inc)))

             :t05
             (let [r (:r action)
                   kind (:kind action)
                   id [:o (:next-obligation state)]
                   ob {:kind kind :debtor (:debtor action)
                       :creditor [:run world-id r]
                       :standing? (contains? #{:track :await-reactive} kind)
                       :slot (if (= kind :track) :consumed :armed)}]
               (-> state
                   (assoc-in [:runs r :status]
                             (if (= kind :track) :running :parked))
                   (add-obligation id ob)
                   (update :next-obligation inc)))

             :t06
             (let [id (:o action)
                   ob (get-in state [:obligations id])
                   r (nth (:creditor ob) 2)]
               (-> (if (:standing? ob)
                     (assoc-in state [:obligations id :slot] :consumed)
                     (remove-obligation state id))
                   (assoc-in [:runs r :status] :running)))

             (throw (ex-info "Unsupported transition" {:action action}))))))

(defn- projection [scopes entities runs obligations]
  {:scopes (into {} (map (fn [[id row]]
                           [id (select-keys row [:kind :parent :status])])) scopes)
   :entities (into {} (map (fn [[id row]]
                             [id (select-keys row [:kind :owner :completed?])])) entities)
   :runs (into {} (map (fn [[id row]]
                         [id (select-keys row [:spin :owner :status])])) runs)
   :obligations (into {} (map (fn [[id row]]
                                [id (select-keys row [:kind :debtor :creditor
                                                      :standing? :slot])])) obligations)})

(defn verify!
  "Check each published state against the independent lifetime model."
  ([] (verify! transition!))
  ([transition]
   (let [child [:spin 0]
         parent [:spin 1]
         scope [:scope 0]
         actions [{:t :t12 :w world-id :scope scope :parent root-id}
                  {:t :t04 :w world-id :e child :scope scope :mode :callback}
                  {:t :t04 :w world-id :e parent :mode :callback}
                  {:t :t05 :w world-id :r [parent 1] :kind :await-once
                   :debtor [:entity world-id child]}
                  {:t :t06 :w world-id :o [:o 2]}
                  {:t :t02 :w world-id :e [:signal 0] :value 1}
                  {:t :t05 :w world-id :r [parent 1] :kind :track
                   :debtor [:entity world-id [:signal 0]]}]
         world (new-world)]
     (loop [reference (model/init-state) actions actions]
       (when-let [action (first actions)]
         (let [reference (model/step reference action)
               actual (transition world action)
               row (get-in reference [:worlds world-id])
               expected (projection (:scopes row) (:entities row) (:runs row)
                                    (:obligations row))
               observed (projection (:scopes actual) (:entities actual) (:runs actual)
                                    (:obligations actual))]
           (when-not (= expected observed)
             (throw (ex-info "Reference mismatch"
                             {:action action :expected expected :observed observed})))
           (doseq [[id ob] (:obligations actual)]
             (when-not (and (contains? (get-in actual [:by-creditor (:creditor ob)]) id)
                            (contains? (get-in actual [:by-debtor (:debtor ob)]) id))
               (throw (ex-info "Obligation index mismatch" {:id id :ob ob}))))
           (recur reference (next actions)))))
     (let [fork (snapshot-copy world)
           basis @fork]
       (transition world {:t :t05 :r [parent 1] :kind :await-once
                          :debtor [:entity world-id child]})
       (when-not (= basis @fork)
         (throw (ex-info "Published snapshot changed with parent" {}))))
     true)))

(defn measure!
  "Cost of one parked await registration and its one-shot resume. This is
   a kernel transaction measurement, not an end-to-end Spin benchmark."
  ([operations] (measure! transition! operations))
  ([transition operations]
   (let [world (new-world)
         child [:spin 0]
         parent [:spin 1]
         _ (transition world {:t :t04 :e child :mode :callback})
         _ (transition world {:t :t04 :e parent :mode :callback})
         debtor [:entity world-id child]
         ^ThreadMXBean bean (ManagementFactory/getThreadMXBean)
         tid (.getId (Thread/currentThread))
         step! (fn []
                 (let [o [:o (:next-obligation @world)]]
                   (transition world {:t :t05 :r [parent 1] :kind :await-once
                                      :debtor debtor})
                   (transition world {:t :t06 :o o})))]
     (.setThreadAllocatedMemoryEnabled bean true)
     (dotimes [_ 2000] (step!))
     (let [before (.getThreadAllocatedBytes bean tid)
           start (System/nanoTime)]
       (dotimes [_ operations] (step!))
       {:ns-per-cycle (/ (double (- (System/nanoTime) start)) operations)
        :bytes-per-cycle (/ (double (- (.getThreadAllocatedBytes bean tid) before)) operations)
        :remaining-obligations (count (:obligations @world))}))))
