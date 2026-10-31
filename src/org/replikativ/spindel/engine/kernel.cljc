(ns org.replikativ.spindel.engine.kernel
  "Transition kernel under construction. Owns canonical lifetime rows and
  indexes in an owned store; never invokes user continuations under its gate."
  (:require [clojure.set :as set]
            [org.replikativ.spindel.engine.owned-store :as store]
            [org.replikativ.spindel.engine.owned-rows :as cells]))

(def ^:private environment ::environment)
(def ^:private world-tables #{:entities :runs :obligations :scopes})

(defn- index-add [index k id] (update index k (fnil conj #{}) id))

(defn- creditor-table [creditor]
  (case (first creditor) :run :by-run-creditor :host :by-host-creditor :by-entity-creditor))
(defn- creditor-id [creditor]
  (if (= :host (first creditor)) (second creditor) (nth creditor 2)))
(defn- debtor-table [w debtor]
  (if (and (= :entity (first debtor)) (= w (second debtor))) :by-local-debtor :by-foreign-debtor))
(defn- debtor-id [w debtor]
  (if (and (= :entity (first debtor)) (= w (second debtor))) (nth debtor 2) debtor))

(defn- encode-world [world]
  (let [obs (:obligations world)
        indexes (reduce-kv (fn [tables o ob]
                             (-> tables
                                 (update (creditor-table (:creditor ob)) (fnil index-add {}) (creditor-id (:creditor ob)) o)
                                 (update (debtor-table (:id world) (:debtor ob)) (fnil index-add {}) (debtor-id (:id world) (:debtor ob)) o)
                                 (cond-> (and (= :entity (first (:debtor ob)))
                                              (not= (:id world) (second (:debtor ob))))
                                   (update :by-debtor-world (fnil index-add {}) (second (:debtor ob)) o))))
                           {} obs)]
    (merge (select-keys world world-tables)
           indexes
           {:header {:world (apply dissoc world world-tables)}
            :runs-by-spin (reduce-kv #(index-add %1 (:spin %3) %2) {} (:runs world))
            :runs-by-owner (reduce-kv #(index-add %1 (:owner %3) %2) {} (:runs world))
            :spawned-by (reduce-kv (fn [index r row]
                                     (reduce #(index-add %1 %2 r) index (:spawned row)))
                                   {} (:runs world))
            :created-by (reduce-kv (fn [index r row]
                                     (reduce #(index-add %1 %2 r) index (:creations row)))
                                   {} (:runs world))
            :entities-by-owner (reduce-kv #(index-add %1 (:owner %3) %2) {} (:entities world))
            :scopes-by-parent (reduce-kv #(index-add %1 (:parent %3) %2) {} (:scopes world))})))

(defn restore
  "Restore a canonical semantic snapshot. Derived obligation indexes rebuild
  here, never by scanning during an ordinary registration or delivery."
  ([state] (restore state {}))
  ([state {:keys [cells? diagnostics?] :or {diagnostics? true}}]
   (store/create-store
    (assoc (reduce-kv #(assoc %1 %2 (encode-world %3)) {} (:worlds state))
           environment {:state {:root (cond-> (dissoc state :worlds)
                                        (not diagnostics?) (assoc :events []))}})
    {:cell-tables (when cells? world-tables) :diagnostics? diagnostics?})))

(defn snapshot [kernel]
  (let [view (store/snapshot kernel)]
    (assoc (get-in view [environment :state :root]) :worlds
           (reduce-kv (fn [worlds w tables]
                        (if (= environment w) worlds
                            (let [header (get-in tables [:header :world])]
                              (assoc worlds w
                                     (if (= :released (:status header))
                                       ;; Empty storage tables are not logical
                                       ;; tombstone fields. Never hide a live
                                       ;; row if an implementation corrupts it.
                                       (merge header (into {} (filter (comp seq val))
                                                           (select-keys tables world-tables)))
                                       (merge header (merge (zipmap world-tables (repeat {}))
                                                            (select-keys tables world-tables))))))))
                      {} view))))

(defn create-kernel
  ([] (create-kernel {}))
  ([options]
   (let [w [:w 0]
         lineage {:parent nil :root w :mode :root :cut nil :basis nil}]
     (restore {:worlds {w {:id w :lineage lineage
                           :status :live :admission :open :seal-seq nil :root [:root w]
                           :next-scope 0 :scope-balance 0
                           :scopes {[:root w] {:kind :world-root :parent nil :status :open}}
                           :entities {} :runs {} :obligations {} :releasing #{}
                           :fdeps #{} :pins #{} :queue []}}
               :registry #{w} :known-worlds #{w} :lineages {w lineage}
               :caps {} :records {} :durable {:caps {} :records {}}
               :custody {:by-holder {} :claims {}} :next-claim 0 :recovery-epoch 0 :process-live? true
               :env {:handles {} :threads {:host {:world w :scope nil :run nil
                                                  :read-permits #{} :excl-permits []}}
                     :native {} :outside [] :principals (set (:external-principals options))}
               :serial {} :events []} options))))

(defn query-row
  "Read an immutable row under the store gate without sealing its table."
  [kernel world table id]
  (store/transact! kernel #(store/read-row % world table id)))

(defn query-field [kernel world table id key]
  (store/transact! kernel #(get (store/read-live-row % world table id) key)))

(defn- read-row [ctx w table id]
  (store/read-live-row (:tx ctx) w table id))

(defn- entity-obligations [ctx w dw e]
  (if (= w dw)
    (read-row ctx w :by-local-debtor e)
    (read-row ctx w :by-foreign-debtor [:entity dw e])))

(defn- mark! [ctx w e]
  (when (and e (:work ctx))
    (let [key [w e]]
      (when-not (contains? @(:work-set ctx) key)
        (vswap! (:work-set ctx) conj key)
        (vswap! (:work ctx) conj key)))))

(defn- mark-owner! [ctx w scope]
  (loop [scope scope seen #{}]
    (when-let [run (when-not (seen scope) (read-row ctx w :runs scope))]
      (mark! ctx w (:spin run))
      (recur (:owner run) (conj seen scope)))))

(defn- mark-row! [ctx w table id old value]
  (case table
    :entities
    (when (or (not (identical? (:kind old) (:kind value)))
              (not (identical? (:owner old) (:owner value)))
              (not (identical? (:completed? old) (:completed? value)))
              (not (identical? (:kept? old) (:kept? value)))
              (not (identical? (:tokens old) (:tokens value)))
              (not (identical? (:reference? old) (:reference? value))))
      (mark! ctx w id)
      (mark-owner! ctx w (:owner old))
      (mark-owner! ctx w (:owner value)))
    :runs
    (let [before (:status old) after (:status value)
          active? #{:running :parked :inherited :stale}
          work? #{:running :parked :inherited}]
      (when (or (not= (:spin old) (:spin value))
                (not= (boolean (active? before)) (boolean (active? after)))
                (not= (= :completed before) (= :completed after)))
        (mark! ctx w (:spin old))
        (mark! ctx w (:spin value)))
      (when (or (not= (boolean (work? before)) (boolean (work? after)))
                (not= (= :unwinding before) (= :unwinding after)))
        (doseq [e (read-row ctx w :entities-by-owner id)] (mark! ctx w e)))
      (when (or (nil? old) (nil? value) (not= (:owner old) (:owner value))
                (not= (= :unwinding before) (= :unwinding after)))
        (mark-owner! ctx w (:owner old))
        (mark-owner! ctx w (:owner value))))
    :obligations
    (doseq [field [:debtor :creditor]
            :when (not (identical? (get old field) (get value field)))
            endpoint [(get old field) (get value field)]
            :let [[kind dw e] endpoint]
            :when (= :entity kind)]
      (mark! ctx dw e))
    nil))

(declare revoke-timer! index-add! index-remove! detach-mailbox-consumer! mailbox-control queue-mailbox-rejection!)

(defn- index-run-links! [ctx w r old value]
  (doseq [[field index] [[:spawned :spawned-by] [:creations :created-by]]
          :let [before (get old field #{}) after (get value field #{})]
          :when (not (identical? before after))]
    (doseq [id before :when (not (contains? after id))]
      (index-remove! ctx w index id r))
    (doseq [id after :when (not (contains? before id))]
      (index-add! ctx w index id r))))

(defn- put! [ctx w table id value]
  (let [old (read-row ctx w table id)]
    (when-not (identical? old value)
      (store/put-row! (:tx ctx) w table id value)
      (when (= :runs table) (index-run-links! ctx w id old value))
      (mark-row! ctx w table id old value)))
  value)

(defn- delete! [ctx w table id]
  (when-let [old (read-row ctx w table id)]
    (store/delete-row! (:tx ctx) w table id)
    (when (= :runs table) (index-run-links! ctx w id old nil))
    (mark-row! ctx w table id old nil)))

(defn- mark-field! [ctx w table id row key before after]
  (case table
    :entities
    (when (#{:kind :owner :completed? :kept? :tokens :reference?} key)
      (mark! ctx w id)
      (if (= key :owner)
        (do (mark-owner! ctx w before) (mark-owner! ctx w after))
        (mark-owner! ctx w (:owner row))))
    :runs
    (case key
      :status
      (let [active? #{:running :parked :inherited :stale}
            work? #{:running :parked :inherited}]
        (when (or (not= (boolean (active? before)) (boolean (active? after)))
                  (not= (= :completed before) (= :completed after)))
          (mark! ctx w (:spin row)))
        (when (or (not= (boolean (work? before)) (boolean (work? after)))
                  (not= (= :unwinding before) (= :unwinding after)))
          (doseq [e (read-row ctx w :entities-by-owner id)] (mark! ctx w e)))
        (when (not= (= :unwinding before) (= :unwinding after))
          (mark-owner! ctx w (:owner row))))
      :owner (do (mark-owner! ctx w before) (mark-owner! ctx w after))
      :spin (do (mark! ctx w before) (mark! ctx w after))
      (:spawned :creations)
      (let [index (if (= key :spawned) :spawned-by :created-by)]
        (doseq [child before :when (not (contains? after child))]
          (index-remove! ctx w index child id))
        (doseq [child after :when (not (contains? before child))]
          (index-add! ctx w index child id)))
      nil)
    :obligations
    (when (#{:debtor :creditor} key)
      (when (= :entity (first before)) (mark! ctx (second before) (nth before 2)))
      (when (= :entity (first after)) (mark! ctx (second after) (nth after 2))))
    nil))

(defn- edit-field! [ctx w table id key value]
  (let [row (read-row ctx w table id)
        before (get row key)]
    (when (or (not (identical? before value)) (not (contains? row key)))
      (mark-field! ctx w table id row key before value)
      (store/write-field! (:tx ctx) w table id key value))))

(defn- edit! [ctx w table id f & args]
  (let [row (read-row ctx w table id)]
    (if (cells/row? row)
      (cond
        (identical? f assoc)
        (do (loop [args args]
              (when (seq args)
                (edit-field! ctx w table id (first args) (second args))
                (recur (nnext args))))
            (read-row ctx w table id))
        (identical? f update)
        (let [[key updater & more] args]
          (edit-field! ctx w table id key (apply updater (get row key) more))
          (read-row ctx w table id))
        :else (put! ctx w table id (apply f row args)))
      (put! ctx w table id (apply f row args)))))

(defn- root-state [ctx] (read-row ctx environment :state :root))
(defn- root-edit! [ctx f & args]
  (apply edit! ctx environment :state :root f args))
(defn- header [ctx w] (read-row ctx w :header :world))
(defn- header-edit! [ctx w f & args]
  (apply edit! ctx w :header :world f args))

(defn- require! [test error data]
  (when-not test (throw (ex-info (name error) (assoc data :error error)))))

(defn- command! [ctx command] (vswap! (:commands ctx) conj command))

(defn- emit! [ctx event]
  (when (:diagnostics? ctx)
    (vswap! (:events ctx) conj (cond-> event (:ob event) (update :ob cells/value))))
  (case (:event event)
    :host-delivery
    (command! ctx (assoc event :op :host
                         :value (if (contains? event :value) (:value event)
                                    (:result (read-row ctx (:world event) :entities (:e event))))))
    :obligation-exit (command! ctx {:op :release-obligation :world (:world event)
                                    :o (:o event) :cause (:cause event)})
    nil))

(defn- enqueue! [ctx w event]
  (require! (not= :fenced (:admission (header ctx w)))
            ::fenced-enqueue-not-implemented {:w w})
  (let [n (inc (max (get (header ctx w) :seq 0)
                    (get-in (root-state ctx) [:clocks w] 0)))]
    (root-edit! ctx assoc-in [:clocks w] n)
    (let [event (assoc event :seq n)]
      (header-edit! ctx w update :queue
                    (fn [events]
                      (conj (if (:source-change? event)
                              (vec (remove #(and (:source-change? %)
                                                 (= (:debtor-world event) (:debtor-world %))
                                                 (= (:completion event) (:completion %))) events))
                              events) event))))))

(defn- allocate! [ctx tag]
  (let [n (get-in (root-state ctx) [:serial tag] 0)]
    (root-edit! ctx assoc-in [:serial tag] (inc n))
    [tag n]))

(defn- index-add! [ctx w table key id]
  (edit! ctx w table key (fnil conj #{}) id))

(defn- index-remove! [ctx w table key id]
  (let [remaining (disj (read-row ctx w table key) id)]
    (if (seq remaining)
      (put! ctx w table key remaining)
      (store/delete-row! (:tx ctx) w table key))))

(defn- add-obligation! [ctx w o ob]
  (put! ctx w :obligations o ob)
  (index-add! ctx w (creditor-table (:creditor ob)) (creditor-id (:creditor ob)) o)
  (index-add! ctx w (debtor-table w (:debtor ob)) (debtor-id w (:debtor ob)) o)
  (when (and (= :entity (first (:debtor ob))) (not= w (second (:debtor ob))))
    (index-add! ctx w :by-debtor-world (second (:debtor ob)) o)))

(defn- pending-events [ctx w]
  (concat (:queue (header ctx w))
          (map :event (filter #(= w (:w %)) (get-in (root-state ctx) [:env :outside])))))

(defn- cancelling? [ctx w o]
  (or (= [w o] (:cancel-delivery ctx))
      (some #(= o (:cancelled %)) (pending-events ctx w))))

(defn- pending-start? [ctx v o ob]
  (let [[kind w e] (:debtor ob)]
    (and (= :entity kind) (not= w v)
         (some #(or (and (= e (:start-for %)) (= v (:creditor-world %)) (= o (:o %)))
                    (and (= v (:join-bundle %)) (= e (get-in % [:members o :debtor]))))
               (pending-events ctx w)))))

(defn- known-foreign-obligation? [ctx w v o ob]
  (let [e (nth (:debtor ob) 2)
        dependencies (:fdeps (header ctx w))]
    (or (pending-start? ctx v o ob)
        (contains? dependencies [e v o])
        (some (fn [[tag target debtors]]
                (and (= :bundle tag) (= v target) (contains? debtors e)))
              dependencies))))

(defn- cleanup-dependency! [ctx dw fd]
  (when (and (not= :released (:status (header ctx dw)))
             (not (contains? (:releasing (header ctx dw)) fd)))
    (header-edit! ctx dw update :fdeps disj fd)
    (header-edit! ctx dw update :releasing conj fd)
    (enqueue! ctx dw {:fdep-ended fd})
    (doseq [e (if (= :bundle (first fd)) (nth fd 2) [(first fd)])]
      (mark! ctx dw e))))

(defn- sync-bundle! [ctx dw v]
  (let [fds (:fdeps (header ctx dw))
        old (first (filter #(and (= :bundle (first %)) (= v (second %))) fds))]
    ;; Every admitted inherited foreign edge is already covered by a bundle.
    ;; Without one there is nothing to synchronize or release.
    (when old
      (let [debtors (set (for [o (read-row ctx v :by-debtor-world dw)
                               :let [ob (read-row ctx v :obligations o)]
                               :when (and (= :run (first (:creditor ob)))
                                          (not (pending-start? ctx v o ob)) (not (cancelling? ctx v o))
                                          (= :inherited (:status (read-row ctx v :runs (nth (:creditor ob) 2)))))]
                           (nth (:debtor ob) 2)))
            ordinary (set (for [[e target _] fds :when (and (not= :bundle e) (= v target))] e))
            ended (set/difference (nth old 2) debtors ordinary)]
        (header-edit! ctx dw update :fdeps disj old)
        (when (seq debtors) (header-edit! ctx dw update :fdeps conj [:bundle v debtors]))
        (when (seq ended) (cleanup-dependency! ctx dw [:bundle v ended]))))))

(defn- add-fdep! [ctx w o]
  (let [ob (read-row ctx w :obligations o)
        [kind dw e] (:debtor ob)]
    (when (and (= :entity kind) (not= w dw) (= :run (first (:creditor ob)))
               (not= :released (:status (header ctx dw)))
               (not (pending-start? ctx w o ob)) (not (cancelling? ctx w o)))
      (if (= :inherited (:status (read-row ctx w :runs (nth (:creditor ob) 2))))
        (let [old (first (filter #(and (= :bundle (first %)) (= w (second %)))
                                 (:fdeps (header ctx dw))))]
          (header-edit! ctx dw update :fdeps disj old)
          (header-edit! ctx dw update :fdeps conj [:bundle w (conj (nth old 2 #{}) e)]))
        (header-edit! ctx dw update :fdeps conj [e w o]))
      (mark! ctx dw e))))

(defn- current-run [ctx w e]
  (last (sort-by second (read-row ctx w :runs-by-spin e))))

(defn- end-obligation!
  ([ctx w o cause] (end-obligation! ctx w o cause nil))
  ([ctx w o cause cancellation]
   (when-let [ob (read-row ctx w :obligations o)]
     (let [[kind dw e] (:debtor ob)]
       (when (and (= :cancel-delivered cause) (= :host (first (:creditor ob))) (= :entity kind) (= dw w))
         (queue-mailbox-rejection! ctx w e [:host o]
                                   (if cancellation (:value cancellation)
                                       :org.replikativ.spindel.engine.protocols/cancelled)))
       (when (and (= :entity kind) (= dw w)
                  (or (= :mailbox (:kind (read-row ctx w :entities e)))
                      (some (fn [[key row]] (and (= w (first key)) (= e (nth key 2 nil)) (= :mailbox (:kind row))))
                            (get-in (root-state ctx) [:env :cleanup-cells]))))
         (let [consumer [(if (= :run (first (:creditor ob))) :obligation :host) o]
               reservation (get-in (mailbox-control ctx w e) [:reservations consumer])]
           (when-not (#{:claimed :entered} (:state reservation))
             (detach-mailbox-consumer! ctx w e consumer)))))
     (let [[ck cw r] (:creditor ob)]
       (when (and (= :cancel-delivered cause) (= :await-reactive (:kind ob))
                  (= :consumed (:slot ob)) (= :run ck)
                  (#{:running :parked :inherited :completed} (:status (read-row ctx cw :runs r)))
                  (= r (current-run ctx cw (first r))))
         (edit! ctx cw :runs r assoc :validation-lost? true)
         (when (:completed? (read-row ctx cw :entities (first r)))
           (edit! ctx cw :entities (first r) assoc :dirty? true))))
     (when (:timer ob) (revoke-timer! ctx (:timer ob)))
     (delete! ctx w :obligations o)
     (index-remove! ctx w (creditor-table (:creditor ob)) (creditor-id (:creditor ob)) o)
     (index-remove! ctx w (debtor-table w (:debtor ob)) (debtor-id w (:debtor ob)) o)
     (when (and (= :entity (first (:debtor ob))) (not= w (second (:debtor ob))))
       (index-remove! ctx w :by-debtor-world (second (:debtor ob)) o))
     (if (:diagnostics? ctx)
       (emit! ctx {:event :obligation-exit :world w :o o :ob ob :cause cause})
       (command! ctx {:op :release-obligation :world w :o o :cause cause}))
     (when (and (= :cancel-delivered cause) (= :host (first (:creditor ob)))
                (let [[_ dw e] (:debtor ob)]
                  (and (not (#{:claimed :entered} (get-in (mailbox-control ctx dw e) [:reservations [:host o] :state])))
                       (not-any? (fn [[_ row]] (and (= :mailbox-callback (:kind row))
                                                    (= [:host o] (:consumer row)) (= :error (:variant row))))
                                 (get-in (root-state ctx) [:env :native])))))
       (emit! ctx {:event :host-delivery :world w :o o
                   :value (if cancellation (:value cancellation) ::cancelled)}))
     (let [[kind dw e] (:debtor ob)
           fd [e w o]]
       (when (and (= :entity kind) (not= w dw) (= :run (first (:creditor ob)))
                  (not= :released (:status (header ctx dw))))
         (when (contains? (:fdeps (header ctx dw)) fd)
           (cleanup-dependency! ctx dw fd))
         (sync-bundle! ctx dw w)))
     (when (and (= :external (:kind ob)) (:token ob))
       (root-edit! ctx assoc-in [:env :waiters (:token ob) :armed?] true))
     ob)))

(defn- touch! [ctx w e tok]
  (when (and tok (read-row ctx w :entities e))
    (edit! ctx w :entities e update :tokens (fnil conj #{}) tok)
    (root-edit! ctx update-in [:env :handles tok :touched] (fnil conj #{}) w)))

(defn- open? [ctx w scope]
  (if-let [run (read-row ctx w :runs scope)]
    (not= :unwinding (:status run))
    (= :open (:status (read-row ctx w :scopes scope)))))

(defn- entity-row [kind owner]
  {:kind kind :origin :created :owner owner :creator nil :completed? false
   :kept? false :result nil :tokens #{} :key nil :order 0})

(defn- put-entity! [ctx w e row]
  (let [old (read-row ctx w :entities e)
        changed? (or (nil? old) (not= (:owner old) (:owner row)))]
    (when (and old changed?)
      (index-remove! ctx w :entities-by-owner (:owner old) e))
    (put! ctx w :entities e row)
    (when changed? (index-add! ctx w :entities-by-owner (:owner row) e))))

(defn- edit-entity! [ctx w e f & args]
  (let [before (:owner (read-row ctx w :entities e))]
    (apply edit! ctx w :entities e f args)
    (let [after (:owner (read-row ctx w :entities e))]
      (when-not (= before after)
        (index-remove! ctx w :entities-by-owner before e)
        (index-add! ctx w :entities-by-owner after e)))))

(defn- spin-row [ctx w e owner]
  (assoc (entity-row :spin owner) :tokens
         (set (for [[tok h] (get-in (root-state ctx) [:env :handles])
                    :when (and (= e (:spin h)) (:reachable? h)
                               (contains? (:touched h) w)
                               (not (contains? (:dropped h) w)))] tok))))

(defn- own-reason? [ctx w entity]
  (let [{:keys [kind owner completed? kept?]} entity]
    (and owner (open? ctx w owner)
         (or (#{:signal :atom :deferred :mailbox :keyed-entry :cache-row :fork} kind)
             (and (#{:timer :waiter} kind)
                  (#{:running :parked :inherited} (:status (read-row ctx w :runs owner))))
             (and (= :spin kind) (or (not completed?) kept?))))))

(defn- active-reason? [ctx w e]
  (some #(#{:running :parked :inherited :stale} (:status (read-row ctx w :runs %)))
        (read-row ctx w :runs-by-spin e)))

(defn- obligation-reason? [ctx w e]
  (or (pos? (count (read-row ctx w :by-local-debtor e)))
      (pos? (count (read-row ctx w :by-entity-creditor e)))))

(defn- dependency-reason? [h e]
  (or (some (fn [[x _ d]] (if (= :bundle x) (contains? d e) (= x e))) (:fdeps h))
      (some (fn [[x _ d]] (if (= :bundle x) (contains? d e) (= x e))) (:releasing h))))

(defn- rooted-liveness [ctx]
  ;; Independent fixed-point implementation for the indexed reference store.
  ;; The native engine maintains an incremental graph instead of sealing tables.
  (let [state (root-state ctx)
        worlds (into {} (for [w (set/union (:registry state) (:known-worlds state))
                              :let [h (header ctx w)]
                              :when (and h (not= :released (:status h)))]
                          [w (merge h (into {} (for [table world-tables]
                                                 [table (store/table-view (:tx ctx) w table)])))]))
        owner (fn [w id] [(if (read-row ctx w :runs id) :run :scope) w id])
        caps (merge (:caps state) (get-in state [:durable :caps]))
        roots (set (mapcat
                    (fn [[w world]]
                      (concat [[:scope w (:root world)]]
                              (for [[r rr] (:runs world)
                                    :when (#{:running :parked :inherited :stale} (:status rr))] [:run w r])
                              (for [[o ob] (:obligations world) :when (= :host (first (:creditor ob)))] [:obligation w o])
                              (for [e (:pins world)] [:entity w e])
                              (for [[e er] (:entities world)
                                    :when (and (= :fork (:kind er)) (not (:reference? er))
                                               (some #(and (= (second e) (:world %))
                                                           (#{:sealed :settling :incomplete} (:disposition %)))
                                                     (vals caps)))] [:entity w e])
                              (for [ev (pending-events ctx w) :when (:register-host ev)] [:entity w (:e ev)])))
                    worlds))]
    (loop [live roots]
      (let [after
            (reduce-kv
             (fn [live w world]
               (let [live (reduce-kv
                           (fn [live id scope]
                             (let [v [:scope w id] p (when-let [p (:parent scope)] (owner w p))]
                               (cond-> live
                                 (and (= :open (:status scope)) p (contains? live p)) (conj v)
                                 (and (= :open (:status scope)) p (contains? live v)) (conj p))))
                           live (:scopes world))
                     live (reduce-kv
                           (fn [live e er]
                             (let [v [:entity w e] p (when-let [p (:owner er)] (owner w p))]
                               (cond-> live
                                 (and p (contains? live v)) (conj p)
                                 (and p (contains? live p) (own-reason? ctx w er)) (conj v))))
                           live (:entities world))
                     live (reduce-kv
                           (fn [live r rr]
                             (if (= :unwinding (:status rr)) live
                                 (let [v [:run w r] e [:entity w (:spin rr)] p (when-let [p (:owner rr)] (owner w p))]
                                   (cond-> live
                                     (contains? live v) (conj e)
                                     (contains? live e) (conj v)
                                     (and p (contains? live v)) (conj p)))))
                           live (:runs world))]
                 (reduce-kv
                  (fn [live o ob]
                    (let [v [:obligation w o] [ck cw creditor] (:creditor ob) [dk dw debtor] (:debtor ob)
                          live (if (or (= :host ck) (contains? live [ck cw creditor])) (conj live v) live)]
                      (cond-> live
                        (and (contains? live v) (= :entity dk) (not (cancelling? ctx w o)))
                        (conj [:entity dw debtor]))))
                  live (:obligations world))))
             live worlds)]
        (if (= after live) live (recur after))))))

(defn- execution-live? [ctx w e]
  (contains? (rooted-liveness ctx) [:entity w e]))

(defn- scope-reason? [ctx w e live]
  (some (fn [r]
          (and (= :completed (:status (read-row ctx w :runs r)))
               (contains? live [:run w r])
               (or (some #(and (not= :unwinding (:status (read-row ctx w :runs %)))
                               (contains? live [:run w %]))
                         (read-row ctx w :runs-by-owner r))
                   (some #(and (not= % e) (contains? live [:entity w %]))
                         (read-row ctx w :entities-by-owner r)))))
        (read-row ctx w :runs-by-spin e)))

(defn- pending-extent? [ctx w e live]
  (let [owner (:owner (read-row ctx w :entities e))]
    (or (and owner (open? ctx w owner)
             (not (or (contains? live [:run w owner])
                      (contains? live [:scope w owner]))))
        (some (fn [r]
                (and (not= :unwinding (:status (read-row ctx w :runs r)))
                     (not (contains? live [:run w r]))))
              (read-row ctx w :runs-by-spin e)))))

(defn- wanted? [ctx w e]
  (let [live (rooted-liveness ctx)]
    (or (contains? live [:entity w e])
        (pending-extent? ctx w e live)
        (dependency-reason? (header ctx w) e))))

(defn- reasons [ctx w e]
  (let [live (rooted-liveness ctx)]
    (cond-> #{}
      (pending-extent? ctx w e live) (conj :extent)
      (and (contains? live [:entity w e]) (own-reason? ctx w (read-row ctx w :entities e))) (conj :own)
      (active-reason? ctx w e) (conj :active)
      (or (some #(contains? live [:obligation w %])
                (concat (read-row ctx w :by-local-debtor e) (read-row ctx w :by-entity-creditor e)))
          (some #(and (:register-host %) (= e (:e %))) (pending-events ctx w))) (conj :obl)
      (dependency-reason? (header ctx w) e) (conj :dep)
      (scope-reason? ctx w e live) (conj :scope)
      (contains? (:pins (header ctx w)) e) (conj :pin))))

(defn- owner [ctx w action]
  (let [thread (get-in (root-state ctx) [:env :threads (get action :th :host)])]
    (or (:scope action) (:scope thread) (:r action) (:run thread) (:root (header ctx w)))))

(defn- reactive? [ctx w r]
  (boolean
   (some (fn [o]
           (let [ob (read-row ctx w :obligations o)]
             (and (:standing? ob) (#{:track :await-reactive} (:kind ob)))))
         (read-row ctx w :by-run-creditor r))))

(declare release-world! cancel-run! supersede! close-scope! resume! rule-l! detach-deferred-wait!
         operation-row operation-barrier? operation-deliver! unlink-operation-registration!)

(defn- owner-chain [ctx w r]
  (loop [id r chain [] seen #{}]
    (let [frozen (get (some-> (:retiring-owners ctx) deref) [w id])]
      (cond
        (nil? id) (conj chain w)
        frozen (into chain frozen)
        (seen id) chain
        (= :unwinding (:status (read-row ctx w :runs id)))
        (into chain (:anchor (read-row ctx w :runs id)))
        :else (recur (or (:owner (read-row ctx w :runs id))
                         (:parent (read-row ctx w :scopes id)))
                     (conj chain id) (conj seen id))))))

(defn- execution-holder [w owner]
  [:execution-owner w
   (cond (= owner [:root w]) :root
         (and (vector? owner) (= 3 (count owner)) (= [:scope :id] (subvec owner 0 2))
              (integer? (nth owner 2)) (not (neg? (nth owner 2)))) :scope
         :else :run)
   owner])

(defn- holder-acquisition! [ctx w owner acceptance]
  (let [holder (execution-holder w owner)
        run? (= :run (nth holder 2))
        row (when run? (read-row ctx w :runs owner))]
    (require! (and (header ctx w) (not= :released (:status (header ctx w)))
                   (if run?
                     (and row (= owner (current-run ctx w (:spin row)))
                          (or (#{:running :parked} (:status row))
                              (and (= :completed (:status row)) (reactive? ctx w owner))))
                     (open? ctx w owner)))
              ::invalid-destination {:holder holder})
    (when run?
      (if (= :running (:status row))
        (let [{:keys [th order]} acceptance
              thread (get-in (root-state ctx) [:env :threads th])]
          (require! (and (= w (:world thread)) (= owner (:run thread)) (:executing? thread)
                         (not (:retired? thread)) (nil? (:cleanup-ticket thread))
                         (integer? order) (not (neg? order)))
                    ::missing-destination-order {:holder holder :acceptance acceptance})
          order)
        :exact-run))))

(defn- cap-row [ctx k]
  (let [state (root-state ctx)]
    (or (get-in state [:durable :caps k]) (get-in state [:caps k]))))

(defn- terminal-cap? [cap]
  (contains? #{:merged :discarded :transferred :partitioned} (:disposition cap)))

(defn- remove-custody! [ctx k holder]
  (let [members (disj (get-in (root-state ctx) [:custody :by-holder holder] #{}) k)]
    (if (seq members)
      (root-edit! ctx assoc-in [:custody :by-holder holder] members)
      (root-edit! ctx update-in [:custody :by-holder] dissoc holder))))

(defn- put-cap! [ctx k cap]
  (let [old (cap-row ctx k)
        durable? (boolean (seq (set/intersection (:scope cap)
                                                 (get-in (root-state ctx) [:model :durable-systems]))))]
    (when (and old (not (terminal-cap? old)))
      (remove-custody! ctx k (:holder old)))
    (root-edit! ctx update :caps dissoc k)
    (root-edit! ctx update-in [:durable :caps] dissoc k)
    (root-edit! ctx assoc-in (if durable? [:durable :caps k] [:caps k]) (assoc cap :durable? durable?))
    (when-not (terminal-cap? cap)
      (root-edit! ctx update-in [:custody :by-holder (:holder cap)] (fnil conj #{}) k))))

(defn- fresh-cap! [ctx k]
  (let [records (merge (:records (root-state ctx)) (get-in (root-state ctx) [:durable :records]))]
    (require! (and k (nil? (cap-row ctx k))
                   (not-any? #(some (fn [desc] (= k (:k desc))) (:successors %)) (vals records)))
              ::cap-id-reused {:k k})))

(defn- operation-reserved? [ctx op]
  (let [state (root-state ctx)]
    (or (contains? (:records state) op)
        (contains? (get-in state [:durable :records]) op)
        (some #(= op (:op %)) (vals (:caps state)))
        (some #(= op (:op %)) (vals (get-in state [:durable :caps])))
        (some #(= op (:settlement-op %)) (vals (get-in state [:custody :claims]))))))

(defn- allocate-custody-claim! [ctx open?]
  (loop [ordinal (:next-claim (root-state ctx))]
    (let [id [:custody-claim ordinal]]
      (if (or (contains? (get-in (root-state ctx) [:custody :claims]) id)
              (and open? (operation-reserved? ctx [:custody-op id])))
        (recur (inc ordinal))
        (do (root-edit! ctx assoc :next-claim (inc ordinal)) id)))))

(defn- enqueue-custody! [ctx w event]
  ;; This committed control message may enter a sealed target. Active cuts
  ;; retain it outside the world until their existing admission fence lifts.
  (when-not (= :released (:status (header ctx w)))
    (let [state (root-state ctx)
          sequence (inc (max (get (header ctx w) :seq 0) (get-in state [:clocks w] 0)))
          held? (and (= :fenced (:admission (header ctx w)))
                     (some #(and (#{:fenced :ready :captured :attached} (:phase %))
                                 (contains? (get-in % [:participants :worlds]) w))
                           (vals (:cuts state))))
          event (assoc event :seq sequence)]
      (root-edit! ctx assoc-in [:clocks w] sequence)
      (if held?
        (root-edit! ctx update-in [:env :outside] conj {:w w :event event})
        (header-edit! ctx w update :queue conj event)))))

(defn- claim-owner-custody! [ctx w owner]
  (let [holder (execution-holder w owner)]
    (doseq [k (sort-by pr-str (get-in (root-state ctx) [:custody :by-holder holder] #{}))]
      (let [cap (cap-row ctx k)
            id (allocate-custody-claim! ctx (= :open (:disposition cap)))
            cleanup-holder [:cleanup id]
            op (if (= :open (:disposition cap)) [:custody-op id] (:op cap))
            kind (if (= :open (:disposition cap)) :discard (:kind cap))]
        (root-edit! ctx assoc-in [:custody :claims id]
                    {:cap k :holder cleanup-holder :origin holder
                     :anchor (mapv #(execution-holder w %) (butlast (owner-chain ctx w owner)))
                     :target-world (:world cap) :kind kind :settlement-op op :phase :dispatch-pending})
        (put-cap! ctx k (assoc cap :holder cleanup-holder :holder-acquisition nil))
        (root-edit! ctx assoc-in [:env :cleanup-targets w id]
                    {:target-world (:world cap) :cap k :op op})
        (enqueue-custody! ctx (:world cap) {:custody-dispatch id :cap k :op op})))))

(defn- physical? [ctx w r]
  (let [env (:env (root-state ctx))]
    (or (some #(and (= w (:world %)) (= r (:run %))) (vals (:threads env)))
        (some #(and (= [w r] (:owner %)) (not= :joined (:state %))
                    (not= :mailbox-callback (:kind %))) (vals (:native env))))))

(defn- cleanup-ticket [w r] [:cps-exit w r])
(defn- cleanup-op? [row] (= :cps-exit (:kind row)))
(defn- protected-native? [row] (#{:cps-exit :cps-finalization} (:kind row)))

(defn- retain-cleanup! [ctx w scope]
  (when (or (get-in (root-state ctx) [:model :cps-exit?])
            (some #(= :mailbox-callback (:kind %)) (vals (get-in (root-state ctx) [:env :native]))))
    (let [owners (loop [pending [scope] found #{}]
                   (if-let [id (peek pending)]
                     (if (found id) (recur (pop pending) found)
                         (recur (into (pop pending) (concat (read-row ctx w :runs-by-owner id)
                                                            (read-row ctx w :scopes-by-parent id)))
                                (conj found id))) found))]
      (doseq [r owners :let [row (read-row ctx w :runs r) n (cleanup-ticket w r)]
              :when (and (get-in (root-state ctx) [:model :cps-exit?]) (:cps-entered? row) (#{:running :parked :stale} (:status row))
                         (not (cleanup-op? (get-in (root-state ctx) [:env :native n]))))]
        (root-edit! ctx update-in [:env :native n]
                    #(assoc (or % {:owner [w r] :state :running :phase :ready
                                   :sequence (:finalization-sequence row 0)})
                            :kind :cps-exit :retired? true :anchor (owner-chain ctx w r))))
      (root-edit! ctx update-in [:env :native]
                  (fn [rows]
                    (into {} (map (fn [[n row]]
                                    [n (cond-> row
                                         (and (= :mailbox-callback (:kind row)) (= w (first (:owner row)))
                                              (some owners (:anchor row))) (assoc :retired? true))]) rows))))
      (let [state (root-state ctx)
            participants (set (for [[n row] (get-in state [:env :native])
                                    :when (and (cleanup-op? row) (= w (first (:owner row)))
                                               (some owners (:anchor row)))] n))
            captured (into {} (for [owner owners e (read-row ctx w :entities-by-owner owner)
                                    :let [row (read-row ctx w :entities e)]
                                    :when (#{:signal :atom :deferred :mailbox} (:kind row))]
                                [[w owner e] (cond-> {:kind (:kind row) :result (:result row)}
                                               (= :deferred (:kind row))
                                               (assoc :allocation (:allocation row)
                                                      :deferred (assoc (:deferred row) :assigned? (:completed? row)))
                                               (= :mailbox (:kind row))
                                               (assoc :allocation (:allocation row) :mailbox (:mailbox row)))]))
            keys (into (set (keys captured))
                       (mapcat #(get-in state [:env :native % :cells]) participants))]
        (when (seq participants)
          (doseq [key keys]
            (let [old (get-in (root-state ctx) [:env :cleanup-cells key])
                  payload (assoc (or old (get captured key))
                                 :holders (into (:holders old #{}) participants))]
              (root-edit! ctx assoc-in [:env :cleanup-cells key] payload)
              (doseq [n participants]
                (root-edit! ctx update-in [:env :native n :cells] (fnil conj #{}) key)))))))))

(defn- finalization-wait! [ctx {:keys [th]}]
  (let [{:keys [world run executing?]} (get-in (root-state ctx) [:env :threads th])
        rr (read-row ctx world :runs run) n (cleanup-ticket world run)
        sequence (inc (:finalization-sequence rr 0))]
    (require! (get-in (root-state ctx) [:model :cps-exit?]) ::profile-disabled {})
    (require! (and executing? (:cps-entered? rr) (= :running (:status rr))
                   (= run (current-run ctx world (:spin rr))))
              ::not-current-slice {:th th})
    (require! (nil? (get-in (root-state ctx) [:env :native n])) ::already-waiting {:n n})
    (edit! ctx world :runs run assoc :status :parked :finalization-sequence sequence)
    (root-edit! ctx assoc-in [:env :native n]
                {:kind :cps-finalization :owner [world run] :state :running
                 :phase :waiting :sequence sequence :retired? false :anchor (owner-chain ctx world run)})))

(defn- release-cleanup-cells! [ctx n]
  (require! (operation-barrier? (get-in (root-state ctx) [:env :native n]))
            ::operation-still-physical {:n n})
  (doseq [key (get-in (root-state ctx) [:env :native n :cells])]
    (let [holders (disj (get-in (root-state ctx) [:env :cleanup-cells key :holders]) n)]
      (if (seq holders)
        (root-edit! ctx assoc-in [:env :cleanup-cells key :holders] holders)
        (root-edit! ctx update-in [:env :cleanup-cells] dissoc key)))))

(defn- finalization-resume! [ctx {:keys [n th] :as action}]
  (let [state (root-state ctx) row (get-in state [:env :native n]) [w r] (:owner row)
        rr (read-row ctx w :runs r) thread (get-in state [:env :threads th])
        inline? (and (:executing? thread) (= [w r] [(:world thread) (:run thread)]))]
    (require! (and (= :cps-finalization (:kind row)) (= :ready (:phase row)) (operation-barrier? row)) ::not-ready {:n n})
    (require! (= w (:w action)) ::wrong-world {:n n :w (:w action)})
    (require! (and (= :parked (:status rr)) (= r (current-run ctx w (:spin rr))))
              ::not-current-slice {:n n})
    (require! (or inline? (nil? (:run thread))) ::thread-busy {:th th})
    (require! (or inline? (not-any? #(and (= w (:world %)) (= r (:run %)))
                                    (vals (:threads (:env state))))) ::slice-busy {:w w :r r})
    (detach-deferred-wait! ctx n)
    (release-cleanup-cells! ctx n)
    (root-edit! ctx update-in [:env :native] dissoc n)
    (edit! ctx w :runs r assoc :status :running)
    (when-not inline?
      (root-edit! ctx assoc-in [:env :threads th]
                  (merge thread {:world w :scope r :run r :obligation-world w :executing? true})))))

(defn- cleanup-claim! [ctx {:keys [n th]}]
  (let [state (root-state ctx) row (get-in state [:env :native n]) [w r] (:owner row)]
    (require! (and (cleanup-op? row) (= :ready (:phase row)) (operation-barrier? row)) ::not-ready {:n n})
    (require! (nil? (get-in state [:env :threads th :run])) ::thread-busy {:th th})
    (require! (not-any? #(and (= w (:world %)) (= r (:run %)))
                        (vals (get-in state [:env :threads]))) ::slice-busy {:w w :r r})
    (detach-deferred-wait! ctx n)
    (root-edit! ctx assoc-in [:env :native n :phase] :claimed)
    (root-edit! ctx update-in [:env :threads th] merge
                {:world w :scope r :run r :executing? true :retired? true
                 :obligation-world w :anchor (:anchor row) :cleanup-ticket n})))

(defn- cleanup-adopt! [ctx {:keys [n th]}]
  (let [state (root-state ctx) row (get-in state [:env :native n])
        thread (get-in state [:env :threads th])]
    (require! (and (cleanup-op? row) (= :ready (:phase row)) (operation-barrier? row)) ::not-ready {:n n})
    (require! (and (:executing? thread) (= (:owner row) [(:world thread) (:run thread)])
                   (nil? (:cleanup-ticket thread))) ::wrong-slice {:n n :th th})
    (detach-deferred-wait! ctx n)
    (root-edit! ctx assoc-in [:env :native n :phase] :claimed)
    (root-edit! ctx update-in [:env :threads th] assoc :cleanup-ticket n
                :retired? true :anchor (:anchor row))))

(defn- cleanup-boundary! [ctx {:keys [th]} phase]
  (let [n (get-in (root-state ctx) [:env :threads th :cleanup-ticket])
        row (get-in (root-state ctx) [:env :native n])]
    (require! (and n (= :claimed (:phase row))) ::not-claimed {:th th})
    (detach-deferred-wait! ctx n)
    (root-edit! ctx update-in [:env :native n]
                #(cond-> (-> % (assoc :phase phase) (dissoc :delivery))
                   (= :waiting phase) (update :sequence inc)))))

(defn- cleanup-deliver! [ctx {:keys [n sequence value]}]
  (let [row (get-in (root-state ctx) [:env :native n])]
    (when (and (protected-native? row) (nil? (:operation row))
               (= :waiting (:phase row)) (= sequence (:sequence row)))
      (detach-deferred-wait! ctx n)
      (root-edit! ctx update-in [:env :native n] assoc :phase :ready :delivery value))))

(defn- cleanup-access! [ctx {:keys [th cell value op frame callback] :as action}]
  (let [n (or callback (when op (first op)) (get-in (root-state ctx) [:env :threads th :cleanup-ticket]))
        row (get-in (root-state ctx) [:env :native n]) participant (operation-row ctx op)
        admitted? (cond op (and participant (contains? (:frames participant) frame))
                        callback (and (= :mailbox-callback (:kind row)) (= frame (:frame row))
                                      (= :executing (:phase row)) (:physical? row))
                        :else (= :claimed (:phase row)))]
    (require! (and n admitted? (contains? (:cells row #{}) cell)
                   (contains? (get-in (root-state ctx) [:env :cleanup-cells cell :holders] #{}) n))
              ::missing-cleanup-cell {:th th :cell cell :op op :frame frame})
    (when (contains? action :value)
      (require! (not (#{:deferred :mailbox} (get-in (root-state ctx) [:env :cleanup-cells cell :kind])))
                ::not-mutable-cleanup-cell {:cell cell})
      (root-edit! ctx assoc-in [:env :cleanup-cells cell :result] value))))

(defn- cleanup-exit! [ctx thread]
  (when-let [n (:cleanup-ticket thread)]
    (let [row (get-in (root-state ctx) [:env :native n])]
      (require! (#{:ready :waiting :returning} (:phase row)) ::missing-cleanup-boundary
                {:n n :phase (:phase row)})
      (when (= :returning (:phase row))
        (detach-deferred-wait! ctx n)
        (release-cleanup-cells! ctx n)
        (root-edit! ctx update-in [:env :native] dissoc n)))))

(defn- remove-run! [ctx w r]
  (when-let [rr (read-row ctx w :runs r)]
    (index-remove! ctx w :runs-by-spin (:spin rr) r)
    (index-remove! ctx w :runs-by-owner (:owner rr) r)
    (doseq [parent (read-row ctx w :spawned-by r)]
      (when (read-row ctx w :runs parent)
        (edit! ctx w :runs parent update :spawned disj r)))
    (delete! ctx w :runs r)))

(defn- prune-timer! [ctx n]
  (let [{:keys [owner phase install handle frames] :as row} (get-in (root-state ctx) [:env :native n])
        [w r] owner]
    (when (and (= :timer-resource (:kind row)) (not= :armed phase) (not= :pending install)
               (empty? frames) (#{:none :released :failed} handle))
      (root-edit! ctx update-in [:env :native] dissoc n)
      (when (and (= :unwinding (:status (read-row ctx w :runs r))) (not (physical? ctx w r)))
        (remove-run! ctx w r)))))

(defn- revoke-timer! [ctx n]
  (let [row (get-in (root-state ctx) [:env :native n])]
    (when (and (= :timer-resource (:kind row)) (= :armed (:phase row)))
      (root-edit! ctx update-in [:env :native n]
                  #(cond-> (-> % (assoc :phase :revoked) (dissoc :value))
                     (= :present (:handle %)) (assoc :handle :release-pending)))
      (prune-timer! ctx n))))

(defn- release-entity! [ctx w e]
  (when-let [er (read-row ctx w :entities e)]
    (when (= :mailbox (:kind er))
      (doseq [o (entity-obligations ctx w w e)
              :let [ob (read-row ctx w :obligations o)]
              :when (= :host (first (:creditor ob)))]
        (queue-mailbox-rejection! ctx w e [:host o]
                                  (if-let [cancellation (:release-cancellation ctx)] (:value cancellation)
                                          :org.replikativ.spindel.engine.protocols/cancelled))))
    (if (= :spin (:kind er))
      (edit-entity! ctx w e assoc :owner nil :dirty? true)
      (edit-entity! ctx w e assoc :owner nil))
    (when (= :mailbox (:kind er))
      (root-edit! ctx update-in [:env :native]
                  (fn [rows]
                    (into {} (map (fn [[id row]]
                                    [id (cond-> row
                                          (and (= :mailbox-callback (:kind row)) (= w (first (:owner row)))
                                               (= e (:allocation row))) (assoc :retired? true))]) rows)))))
    (doseq [r (sort-by pr-str (read-row ctx w :runs-by-spin e))
            :when (#{:running :parked :inherited} (:status (read-row ctx w :runs r)))]
      (cancel-run! ctx w r nil))
    (doseq [r (sort-by pr-str (read-row ctx w :runs-by-spin e))
            :when (#{:completed :stale} (:status (read-row ctx w :runs r)))]
      (supersede! ctx w r))
    (doseq [o (entity-obligations ctx w w e)]
      (let [ob (read-row ctx w :obligations o)]
        (when (= :run (first (:creditor ob)))
          (let [reservation (when (= :mailbox (:kind er))
                              (get-in (mailbox-control ctx w e) [:reservations [:obligation o]]))
                r (nth (:creditor ob) 2)]
            (when-not (#{:claimed :entered} (:state reservation))
              (when (and (= :reserved (:state reservation)) (= :running (:status (read-row ctx w :runs r))))
                (edit! ctx w :runs r assoc :status :parked))
              (resume! ctx {:w w :o o :value (if-let [cancellation (:release-cancellation ctx)]
                                               (:value cancellation) ::cancelled)}))))
        (end-obligation! ctx w o :cancel-delivered (:release-cancellation ctx))))))

(defn- release-owned! [ctx w scope]
  (doseq [e (sort-by pr-str (read-row ctx w :entities-by-owner scope))]
    (release-entity! ctx w e)))

(defn- retire-run! [ctx w r cause effects anchor]
  ;; Cascading entity release may revisit this Run while its ancestry row is
  ;; still needed. The outer retirement owns its cause and all Run effects.
  (let [key [w r] retiring (:retiring-owners ctx)]
    (when-not (contains? @retiring key)
      (vswap! retiring assoc key (or anchor (owner-chain ctx w r)))
      (try
        (claim-owner-custody! ctx w r)
        (retain-cleanup! ctx w r)
        (let [rr (if (physical? ctx w r) (cells/value (read-row ctx w :runs r)) (read-row ctx w :runs r))
              chain (get @retiring key)]
          (root-edit! ctx update-in [:env :native]
                      #(into {} (for [[n row] %]
                                  [n (if (and (= :timer-resource (:kind row)) (= [w r] (:owner row)))
                                       (assoc row :retired? true :anchor chain) row)])))
          (doseq [s (sort-by pr-str (read-row ctx w :scopes-by-parent r))]
            (close-scope! ctx w s))
          (doseq [o (read-row ctx w :by-run-creditor r)]
            (end-obligation! ctx w o :creditor-cancelled))
          (root-edit! ctx update-in [:env :native]
                      (fn [ops]
                        (into {} (map (fn [[n row]]
                                        [n (if (and (= [w r] (:owner row)) (not= :joined (:state row))
                                                    (not (protected-native? row)) (not (#{:mailbox-callback :timer-resource} (:kind row))))
                                             (assoc row :state :cancel-requested) row)])) ops)))
          (when (:diagnostics? ctx)
            (emit! ctx {:event :run-exit :world w :r r :cause cause
                        :t (if (= cause :superseded) :t10 :t11)}))
          (effects)
          (remove-run! ctx w r)
          (when (physical? ctx w r)
            (put! ctx w :runs r
                  (assoc rr :status :unwinding :owner nil :anchor chain :retired? true
                         :creations #{} :spawned #{} :pred nil :ancestors #{}))
            (index-add! ctx w :runs-by-spin (:spin rr) r)
            (index-add! ctx w :runs-by-owner nil r)
            (root-edit! ctx update-in [:env :threads]
                        (fn [threads]
                          (into {} (map (fn [[id row]]
                                          [id (cond-> row (and (= w (:world row)) (= r (:run row)))
                                                      (assoc :retired? true))])) threads)))
            (root-edit! ctx update-in [:env :native]
                        (fn [ops]
                          (into {} (map (fn [[id row]]
                                          [id (cond-> row (= [w r] (:owner row)) (assoc :retired? true))])) ops)))
            (doseq [id (read-row ctx w :runs-by-spin (:spin rr))
                    :let [row (read-row ctx w :runs id)]
                    :when (= r (:pred row))]
              (edit! ctx w :runs id assoc :pred nil))
            (doseq [e (:creations rr)
                    :when (= r (:creator (read-row ctx w :entities e)))]
              (edit! ctx w :entities e assoc :creator nil))))
        (finally
          (vswap! retiring dissoc key))))))

(defn- foreign-creditors [ctx w e]
  (set
   (concat
    (mapcat (fn [[tag v payload]]
              (cond
                (= tag e) [[v payload]]
                (and (= :bundle tag) (contains? payload e))
                (map #(vector v %) (entity-obligations ctx v w e))
                :else [])) (:fdeps (header ctx w)))
    (mapcat (fn [event]
              (cond
                (= e (:start-for event)) [[(:creditor-world event) (:o event)]]
                (:join-bundle event)
                (for [[o member] (:members event) :when (= e (:debtor member))]
                  [(:join-bundle event) o])
                :else [])) (pending-events ctx w)))))

(defn- cancel-foreign-debtor!
  ([ctx w v o] (cancel-foreign-debtor! ctx w v o nil))
  ([ctx w v o cancellation]
   (let [e (nth (:debtor (read-row ctx v :obligations o)) 2)
         remove-request (fn [event]
                          (cond
                            (and (= v (:creditor-world event)) (= o (:o event)) (:start-for event)) nil
                            (= v (:join-bundle event))
                            (let [members (dissoc (:members event) o)]
                              (when (seq members)
                                (assoc event :members members :debtors (set (map :debtor (vals members))))))
                            :else event))]
     (header-edit! ctx w update :queue #(vec (keep remove-request %)))
     (root-edit! ctx update-in [:env :outside]
                 #(vec (keep (fn [held]
                               (if (= w (:w held))
                                 (when-let [event (remove-request (:event held))] (assoc held :event event)) held)) %)))
     (header-edit! ctx w update :fdeps disj [e v o])
     (enqueue! ctx v (cond-> {:cancelled o} cancellation (assoc :value (:value cancellation))))
     (when-not (some (fn [other]
                       (let [ob (read-row ctx v :obligations other)]
                         (and (not= o other) (= :run (first (:creditor ob)))
                              (= :inherited (:status (read-row ctx v :runs (nth (:creditor ob) 2))))
                              (not (pending-start? ctx v other ob)) (not (cancelling? ctx v other)))))
                     (entity-obligations ctx v w e))
       (header-edit! ctx w update :fdeps
                     #(set (keep (fn [[tag target debtors :as fd]]
                                   (if (and (= :bundle tag) (= v target))
                                     (when (seq (disj debtors e)) [:bundle v (disj debtors e)]) fd)) %)))))))

(defn- supersede! [ctx w r]
  (when-let [rr (read-row ctx w :runs r)]
    (require! (#{:completed :stale} (:status rr)) ::not-predecessor {:r r})
    (let [chain (owner-chain ctx w r)]
      (retire-run!
       ctx w r :superseded
       (fn []
         (doseq [child (sort-by pr-str (read-row ctx w :runs-by-owner r))]
           (cancel-run! ctx w child (into [child] chain)))
         (doseq [e (read-row ctx w :entities-by-owner r)
                 :when (#{:cache-row :keyed-entry} (:kind (read-row ctx w :entities e)))]
           (index-remove! ctx w :entities-by-owner r e)
           (delete! ctx w :entities e))
         (release-owned! ctx w r))
       chain))))

(defn- cancel-run!
  ([ctx w r anchor] (cancel-run! ctx w r anchor (:release-cancellation ctx)))
  ([ctx w r anchor cancellation]
   (when-let [rr (read-row ctx w :runs r)]
     (when-not (= :unwinding (:status rr))
       (let [e (:spin rr)
             current? (= r (current-run ctx w e))
             chain (or anchor (owner-chain ctx w r))]
         (retire-run!
          ctx w r :cancelled
          (fn []
            (doseq [child (sort-by pr-str (read-row ctx w :runs-by-owner r))]
              (cancel-run! ctx w child (into [child] chain)))
            (when current?
              (if cancellation
               ;; Explicit public cancellation has one stable settlement order
               ;; across host/parent observers, independent of index set order.
                (doseq [[v o] (sort-by #(second (second %))
                                       (concat (map #(vector w %) (entity-obligations ctx w w e))
                                               (foreign-creditors ctx w e)))]
                  (if (= v w)
                    (let [ob (read-row ctx w :obligations o)]
                      (when (= :run (first (:creditor ob)))
                        (resume! ctx {:w w :o o :value (:value cancellation)}))
                      (end-obligation! ctx w o :cancel-delivered cancellation))
                    (cancel-foreign-debtor! ctx w v o cancellation)))
                (do
                  (doseq [o (entity-obligations ctx w w e)]
                    (let [ob (read-row ctx w :obligations o)]
                      (when (= :run (first (:creditor ob)))
                        (resume! ctx {:w w :o o :value ::cancelled}))
                      (end-obligation! ctx w o :cancel-delivered)))
                  (doseq [[v o] (foreign-creditors ctx w e)]
                    (cancel-foreign-debtor! ctx w v o))))
              (when (= :stale (:status (read-row ctx w :runs (:pred rr))))
                (supersede! ctx w (:pred rr))))
            (release-owned! ctx w r)
            (when (read-row ctx w :entities e)
              (edit! ctx w :entities e assoc :dirty? true)))
          chain))))))

(defn- close-scope! [ctx w scope]
  (require! (or (and (vector? scope) (= 3 (count scope))
                     (= [:scope :id] (subvec scope 0 2))
                     (integer? (nth scope 2)) (not (neg? (nth scope 2))))
                (= scope [:root w])) ::invalid-scope-id {:scope scope})
  (if (= scope (:root (header ctx w)))
    (release-world! ctx {:w w})
    (when (and (not (contains? @(:retiring-owners ctx) [w scope]))
               (not= :released (:status (header ctx w))) (open? ctx w scope))
      (vswap! (:retiring-owners ctx) assoc [w scope] (owner-chain ctx w scope))
      (try
        (claim-owner-custody! ctx w scope)
        (retain-cleanup! ctx w scope)
        (doseq [s (sort-by pr-str (read-row ctx w :scopes-by-parent scope))]
          (close-scope! ctx w s))
        (doseq [r (sort-by pr-str (read-row ctx w :runs-by-owner scope))]
          (cancel-run! ctx w r nil))
        (release-owned! ctx w scope)
        (let [parent (:parent (read-row ctx w :scopes scope))]
          (index-remove! ctx w :scopes-by-parent parent scope)
          (delete! ctx w :scopes scope)
          (header-edit! ctx w update :scope-balance dec))
        (finally
          (vswap! (:retiring-owners ctx) dissoc [w scope]))))))

(defn- remove-entity! [ctx w e]
  (when-let [er (read-row ctx w :entities e)]
    (doseq [r (sort-by pr-str (read-row ctx w :runs-by-spin e))]
      (cancel-run! ctx w r nil))
    (index-remove! ctx w :entities-by-owner (:owner er) e)
    (delete! ctx w :entities e)
    (command! ctx {:op :release-entity :world w :e e})
    (header-edit! ctx w update :pins disj e)
    (header-edit! ctx w update :queue
                  #(vec (remove (fn [event]
                                  (or (and (= e (:completion event)) (= w (:debtor-world event)))
                                      (= e (:signal-write event)))) %)))
    (doseq [creator (read-row ctx w :created-by e)]
      (when (read-row ctx w :runs creator)
        (edit! ctx w :runs creator update :creations disj e)))))

(defn- prune-ancestry! [ctx]
  (doseq [w (:known-worlds (root-state ctx))]
    (let [runs (store/table-view (:tx ctx) w :runs)
          relevant (into (set (for [[r rr] runs :when (not= :unwinding (:status rr))] r))
                         (keep :creator (vals (store/table-view (:tx ctx) w :entities))))]
      (doseq [[r row] runs
              :let [ancestors (set (filter relevant (:ancestors row)))]
              :when (not= ancestors (:ancestors row))]
        (edit! ctx w :runs r assoc :ancestors ancestors)))))

(defn- signal-dependent? [ctx w e]
  (loop [todo [[w e]] seen #{}]
    (if-let [[w e :as key] (peek todo)]
      (let [todo (pop todo) er (read-row ctx w :entities e)]
        (cond
          (contains? seen key) (recur todo seen)
          (or (#{:signal :atom :deferred :mailbox} (:kind er)) (:dirty? er)) true
          :else
          (recur (into todo (for [r (read-row ctx w :runs-by-spin e)
                                  o (read-row ctx w :by-run-creditor r)
                                  :let [ob (read-row ctx w :obligations o)
                                        [dk dw de] (:debtor ob)]
                                  :when (and (#{:track :await-reactive} (:kind ob)) (= :entity dk))]
                              [dw de]))
                 (conj seen key))))
      false)))

(defn- idle-retirement-order [ctx w idle]
  ;; Only execution-owner ancestry orders Runs. Entity lifetime release is
  ;; preserved separately by keeping every idle entity owner until phase three.
  (let [idle (set idle)
        selected (set (for [[r row] (store/table-view (:tx ctx) w :runs)
                            :when (and (contains? idle (:spin row))
                                       (#{:completed :stale} (:status row)))] r))
        dependencies
        (into {}
              (for [r selected
                    :let [execution (rest (butlast (owner-chain ctx w r)))]]
                [r (set/intersection selected
                                     (set (filter #(read-row ctx w :runs %)
                                                  execution)))]))]
    (loop [remaining selected result []]
      (if (empty? remaining) result
          (let [ready (sort-by pr-str
                               (filter #(empty? (set/intersection remaining (get dependencies %)))
                                       remaining))]
            (require! (seq ready) ::retirement-precedence-cycle
                      {:w w :runs remaining :dependencies (select-keys dependencies remaining)})
            (recur (apply disj remaining ready) (into result ready)))))))

(defn- rule-l! [ctx]
  ;; The reference sweep is deliberately simple and local. Foreign index
  ;; releases enqueue their debtor-world acknowledgement; they never sweep it.
  (let [w (:acting-world ctx)]
    (when (and w (not= :released (:status (header ctx w))))
      (loop []
        (let [changed? (volatile! false)
              idle (vec (for [[e er] (store/table-view (:tx ctx) w :entities)
                              :when (and (= :spin (:kind er)) (:completed? er)
                                         (not (:cache-gc-only? ctx))
                                         (not (execution-live? ctx w e)))] e))
              ;; Realize proofs and the complete Run plan before mutating the
              ;; graph: parent cancellation may remove a child's dependencies.
              signal-dependent (vec (filter #(signal-dependent? ctx w %) idle))
              retirement (idle-retirement-order ctx w idle)]
          (doseq [e signal-dependent]
            (when-not (:dirty? (read-row ctx w :entities e)) (vreset! changed? true))
            (edit-entity! ctx w e assoc :dirty? true))
          (doseq [r retirement
                  :when (#{:completed :stale} (:status (read-row ctx w :runs r)))]
            (vreset! changed? true)
            (supersede! ctx w r))
          (doseq [e (sort-by pr-str idle)
                  :let [er (read-row ctx w :entities e)]
                  :when er]
            (when (:owner er) (vreset! changed? true))
            (edit-entity! ctx w e assoc :owner nil))
          (let [dead (vec (for [[e er] (store/table-view (:tx ctx) w :entities)
                                :when (and (not (wanted? ctx w e))
                                           (not (and (= :spin (:kind er)) (:completed? er) (seq (:tokens er)))))] e))]
            (doseq [e (sort-by pr-str dead)] (vreset! changed? true) (remove-entity! ctx w e)))
          (when @changed? (recur)))))))

(defn- handle-unreachable! [ctx tok]
  (let [{:keys [reachable? spin touched]} (get-in (root-state ctx) [:env :handles tok])]
    (require! reachable? ::already-unreachable {:tok tok})
    (root-edit! ctx assoc-in [:env :handles tok :reachable?] false)
    (let [notifications (vec (for [w touched
                                   :when (and (contains? (:registry (root-state ctx)) w)
                                              (read-row ctx w :entities spin))]
                               {:t :t17 :w w :e spin :tok tok}))]
      (root-edit! ctx update-in [:env :gc] (fnil into []) notifications)
      (vreset! (:result ctx) {:notifications notifications}))))

(defn- gc-notify! [ctx {:keys [w e tok]}]
  (require! (false? (get-in (root-state ctx) [:env :handles tok :reachable?]))
            ::reachable-handle {:tok tok})
  (root-edit! ctx update-in [:env :gc]
              #(vec (remove (fn [a] (= [w e tok] [(:w a) (:e a) (:tok a)])) %)))
  (when (contains? (:tokens (read-row ctx w :entities e)) tok)
    (edit! ctx w :entities e update :tokens disj tok)))

(defn- release-idle! [ctx {:keys [w es]}]
  (rule-l! ctx)
  (doseq [e (or es (keys (store/table-view (:tx ctx) w :entities)))
          :let [row (read-row ctx w :entities e)]
          :when (and (= :spin (:kind row)) (:completed? row) (not (wanted? ctx w e)))]
    (doseq [tok (:tokens row)]
      (root-edit! ctx update-in [:env :handles tok :dropped] conj w))
    (edit! ctx w :entities e assoc :tokens #{})))

(defn- predecessor? [ctx w previous r]
  (contains? (:ancestors (read-row ctx w :runs r)) previous))

(defn- create-source! [ctx {:keys [w e key value kind order] :or {kind :signal order 0} :as action}]
  (let [scope (owner ctx w action)
        e (if key [:key (get-in (header ctx w) [:lineage :root]) key] e)
        source (loop [v w]
                 (cond (read-row ctx v :entities e) v
                       (and key (get-in (header ctx v) [:lineage :parent]))
                       (recur (get-in (header ctx v) [:lineage :parent]))))]
    (require! (= :live (:status (header ctx w))) ::not-live {:world w})
    (require! (open? ctx w scope) ::closed-scope {:scope scope})
    (if source
      (let [er (read-row ctx source :entities e)]
        (require! (and (= :signal (:kind er)) (= key (:key er))) ::key-collision {:e e})
        (when (and (= source w) (predecessor? ctx w (:owner er) scope))
          (edit-entity! ctx w e assoc :owner scope :order order)
          (edit! ctx w :runs scope update :creations conj e)))
      (do (put-entity! ctx w e (cond-> (assoc (entity-row kind scope) :key key :result value :order order)
                                 (contains? action :allocation) (assoc :allocation (:allocation action))))
          (when (read-row ctx w :runs scope)
            (edit! ctx w :runs scope update :creations conj e))))))

(defn- managed-source? [ctx {:keys [w e allocation]}]
  (let [row (read-row ctx w :entities e)]
    (and (#{:atom :deferred :mailbox} (:kind row)) (some? allocation) (= allocation (:allocation row)))))

(defn- source-unreachable! [ctx {:keys [w e allocation] :as action}]
  ;; Trusted host receipt: all wrappers of this allocation are gone.
  (when (managed-source? ctx action)
    (root-edit! ctx assoc-in [:env :source-gc [w e allocation]] true)))

(defn- source-backing-world [ctx v e]
  (loop [v v seen #{}]
    (when (and v (not (seen v)))
      (cond
        (read-row ctx v :entities e) v
        (= :following (get-in (header ctx v) [:lineage :mode]))
        (recur (get-in (header ctx v) [:lineage :parent]) (conj seen v))))))

(defn- source-in-use? [ctx w e allocation]
  (or (contains? (:pins (header ctx w)) e)
      (some (fn [[reg edge]]
              (let [participant (operation-row ctx (:operation edge))]
                (and (= :open (:state participant))
                     (= :pending (get-in participant [:registrations reg :state])))))
            (get-in (read-row ctx w :entities e) [:deferred :protected]))
      (let [control (:mailbox (read-row ctx w :entities e))]
        (or (seq (:pending control)) (seq (:reservations control)) (seq (:physical control))))
      (seq (get-in (root-state ctx) [:env :cell-claims [w e allocation]]))
      (some
       (fn [v]
         (let [h (header ctx v)]
           (or (some (fn [o]
                       (= [:entity w e] (:debtor (read-row ctx v :obligations o))))
                     (entity-obligations ctx v w e))
               (some #(or (and (= e (:completion %)) (= w (get % :debtor-world v)))
                          (and (= v w) (or (= e (:deferred-assignment %)) (= e (:mailbox-post %))) (= allocation (:allocation %))))
                     (pending-events ctx v))
               (and (= v w)
                    (some (fn [[x _ debtors]] (if (= :bundle x) (contains? debtors e) (= x e)))
                          (:fdeps h)))
               (and (not= v w) (not= :released (:status h))
                    (= w (source-backing-world ctx v e))))))
       (:known-worlds (root-state ctx)))))

(defn- reap-source! [ctx {:keys [w e allocation] :as action}]
  (let [receipt [w e allocation]]
    (when (get-in (root-state ctx) [:env :source-gc receipt])
      (when (managed-source? ctx action)
        (require! (not (source-in-use? ctx w e allocation)) ::source-in-use
                  {:w w :e e :allocation allocation})
        ;; Atom storage has no run to cancel. Leave its owner and protected
        ;; cleanup payloads intact; delete only this world's ordinary cell.
        (let [row (read-row ctx w :entities e)]
          (index-remove! ctx w :entities-by-owner (:owner row) e)
          (delete! ctx w :entities e)
          (doseq [creator (read-row ctx w :created-by e)]
            (when (read-row ctx w :runs creator)
              (edit! ctx w :runs creator update :creations disj e)))
          (command! ctx {:op :release-entity :world w :e e})))
      (root-edit! ctx update-in [:env :source-gc] dissoc receipt))))

(defn- deferred-admitted! [ctx w]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (require! (and (= :open (:admission (header ctx w)))
                 (not-any? #(and (= w (:child %)) (= :attached (:phase %)))
                           (vals (:cuts (root-state ctx))))) ::not-admitted {:world w}))

(defn- deferred-retained [ctx w e allocation cell]
  (let [matches (if cell [cell]
                    (for [[key row] (get-in (root-state ctx) [:env :cleanup-cells])
                          :when (and (= w (first key)) (= e (nth key 2 nil))
                                     (= :deferred (:kind row)) (= allocation (:allocation row))
                                     (seq (:holders row)))] key))]
    (when-let [key (first matches)]
      (let [row (get-in (root-state ctx) [:env :cleanup-cells key])]
        (when (and (= w (first key)) (= e (nth key 2 nil))
                   (= :deferred (:kind row)) (= allocation (:allocation row))
                   (seq (:holders row)))
          {:cell key :row row})))))

(defn- deferred-view [ctx {:keys [w e allocation cell]} fallback?]
  (require! (= allocation e) ::allocation-mismatch {:w w :e e :allocation allocation})
  (let [source (read-row ctx w :entities e)]
    (cond
      cell (deferred-retained ctx w e allocation cell)
      (and (= :deferred (:kind source)) (= allocation (:allocation source)) (:owner source))
      {:row source}
      fallback? (deferred-retained ctx w e allocation nil))))

(defn- admit-deferred-view! [ctx {:keys [w th cell op frame callback]} view]
  (when callback
    (let [receipt (get-in (root-state ctx) [:env :native callback])]
      (require! (and (= :mailbox-callback (:kind receipt)) (= w (first (:owner receipt)))
                     (= frame (:frame receipt)) (:cell view)
                     (contains? (:cells receipt #{}) (:cell view))
                     (contains? (:holders (:row view) #{}) callback))
                ::released-deferred {:callback callback :cell cell})))
  (when op
    (let [participant (operation-row ctx op) ticket (get-in (root-state ctx) [:env :native (first op)])]
      (require! (and participant (= w (first (:owner ticket))) (contains? (:frames participant) frame)
                     (or (not (cleanup-op? ticket)) (:cell view))
                     (or (nil? (:cell view))
                         (and (contains? (:cells ticket #{}) (:cell view))
                              (contains? (:holders (:row view) #{}) (first op)))))
                ::released-deferred {:w w :op op :cell cell})))
  (require! view ::released-deferred {:w w :cell cell})
  (let [thread (get-in (root-state ctx) [:env :threads th]) r (:run thread)
        retired? (= :unwinding (:status (read-row ctx (:world thread) :runs r)))]
    (if (:cell view)
      (when r
        (require! (and cell (= w (:world thread))
                       (contains? (:holders (:row view))
                                  (or (:cleanup-ticket thread) (cleanup-ticket w r))))
                  ::released-deferred {:w w :cell cell :th th}))
      (do (require! (not retired?) ::cancelled {:w w :r r})
          (deferred-admitted! ctx w)))))

(defn- enqueue-deferred! [ctx w event]
  (if (= :released (:status (header ctx w)))
    (let [n (inc (max (get (header ctx w) :seq 0)
                      (get-in (root-state ctx) [:clocks w] 0)))]
      (root-edit! ctx assoc-in [:clocks w] n)
      (root-edit! ctx update-in [:env :outside] conj {:w w :event (assoc event :seq n)}))
    (enqueue! ctx w event)))

(defn- deferred-edit! [ctx w e view f & args]
  (if-let [key (:cell view)]
    (apply root-edit! ctx update-in [:env :cleanup-cells key] f args)
    (apply edit! ctx w :entities e f args))
  ;; The prototype mirrors aliases explicitly; the native engine shares one
  ;; control array across live storage and every retained allocation copy.
  (let [row (if-let [key (:cell view)]
              (get-in (root-state ctx) [:env :cleanup-cells key])
              (read-row ctx w :entities e))
        allocation (:allocation row)
        assigned? (if (:cell view) (get-in row [:deferred :assigned?]) (:completed? row))
        metadata (dissoc (:deferred row) :assigned?)
        source (read-row ctx w :entities e)
        keys (vec (for [[key cell] (get-in (root-state ctx) [:env :cleanup-cells])
                        :when (and (= w (first key)) (= e (nth key 2 nil))
                                   (= :deferred (:kind cell)) (= allocation (:allocation cell)))] key))]
    (when (and (= :deferred (:kind source)) (= allocation (:allocation source)))
      (edit! ctx w :entities e assoc :result (:result row) :completed? assigned? :deferred metadata))
    (doseq [key keys]
      (root-edit! ctx update-in [:env :cleanup-cells key] assoc
                  :result (:result row) :deferred (assoc metadata :assigned? assigned?)))))

(defn- retain-deferred-for-ticket! [ctx w e view n]
  (let [source (read-row ctx w :entities e)
        key (or (:cell view) [w (:owner source) e])
        existing (get-in (root-state ctx) [:env :cleanup-cells key])
        row (or existing {:kind :deferred :allocation (:allocation source) :result (:result source)
                          :deferred (assoc (:deferred source) :assigned? (:completed? source))
                          :holders #{}})]
    (root-edit! ctx assoc-in [:env :cleanup-cells key] (update row :holders (fnil conj #{}) n))
    (root-edit! ctx update-in [:env :native n :cells] (fnil conj #{}) key)
    key))

(defn- detach-deferred-wait! [ctx n]
  (when-let [participant (get-in (root-state ctx) [:env :native n :operation])]
    (require! (operation-barrier? (get-in (root-state ctx) [:env :native n]))
              ::operation-still-physical {:n n})
    (doseq [reg (keys (:registrations participant))]
      (unlink-operation-registration! ctx (:id participant) reg))
    (root-edit! ctx update-in [:env :native n] dissoc :operation)))

(defn- protected-operation-id? [op]
  (and (vector? op) (= 2 (count op)) (vector? (first op))
       (= 3 (count (first op))) (= :cps-exit (ffirst op))))

(defn- operation-row [ctx op]
  (let [row (when (vector? op) (get-in (root-state ctx) [:env :native (first op) :operation]))]
    (when (= op (:id row)) row)))

(defn- operation-barrier? [ticket]
  (let [op (:operation ticket)]
    (or (nil? op) (and (= :terminal (:state op)) (zero? (:physical op)) (empty? (:frames op))))))

(defn- operation-frame! [ctx {:keys [op n sequence frame]}]
  (let [row (operation-row ctx op) ticket (get-in (root-state ctx) [:env :native n])]
    (require! (and row (= n (first op)) (= sequence (second op) (:sequence ticket))
                   (protected-native? ticket) (= :open (:state row)) (contains? (:frames row) frame))
              ::not-operation-frame {:op op :frame frame})
    row))

(defn- unlink-operation-registration! [ctx op reg]
  (when-let [{:keys [w e allocation cell]} (get-in (operation-row ctx op) [:registrations reg])]
    (if (or (= :mailbox (:kind (read-row ctx w :entities e)))
            (= :mailbox (get-in (root-state ctx) [:env :cleanup-cells cell :kind])))
      (detach-mailbox-consumer! ctx w e [:operation reg])
      (when-let [view (or (deferred-retained ctx w e allocation cell)
                          (deferred-view ctx {:w w :e e :allocation allocation} false))]
        (deferred-edit! ctx w e view update-in [:deferred :protected] dissoc reg)))
    (root-edit! ctx update-in [:env :native (first op) :operation :registrations] dissoc reg)))

(defn- operation-start! [ctx {:keys [op n sequence frame]}]
  (let [ticket (get-in (root-state ctx) [:env :native n]) [w r] (:owner ticket)]
    (require! (and (protected-native? ticket) (= :waiting (:phase ticket))
                   (= sequence (:sequence ticket)) (= op [n sequence]) (nil? (:operation ticket))
                   (= frame [op 1])
                   (some #(and (= w (:world %)) (= r (:run %)))
                         (vals (get-in (root-state ctx) [:env :threads]))))
              ::not-operation-start {:n n :op op})
    (root-edit! ctx assoc-in [:env :native n :operation]
                {:id op :state :open :parent r :physical 1 :frames #{frame}
                 :next-registration 0 :next-frame 1 :registrations {}})))

(defn- mailbox-view [ctx {:keys [w e allocation cell]} fallback?]
  (require! (= e allocation) ::allocation-mismatch {:w w :e e :allocation allocation})
  (let [source (read-row ctx w :entities e)
        live? (and (= :mailbox (:kind source)) (= allocation (:allocation source)) (:owner source))
        key (or cell (when (and fallback? (not live?))
                       (first (for [[key row] (get-in (root-state ctx) [:env :cleanup-cells])
                                    :when (and (= w (first key)) (= e (nth key 2 nil))
                                               (= :mailbox (:kind row)) (= allocation (:allocation row))
                                               (seq (:holders row)))] key))))
        retained (when key (get-in (root-state ctx) [:env :cleanup-cells key]))]
    (cond
      (and key (= w (first key)) (= e (nth key 2 nil)) (= :mailbox (:kind retained))
           (= allocation (:allocation retained)) (seq (:holders retained))) {:cell key :row retained}
      key nil
      live? {:row source})))

(defn- mailbox-control [ctx w e]
  (let [source (read-row ctx w :entities e)]
    (if (and (= :mailbox (:kind source)) (= e (:allocation source)))
      (:mailbox source)
      (some (fn [[key row]] (when (and (= w (first key)) (= e (nth key 2 nil))
                                       (= :mailbox (:kind row)) (= e (:allocation row))) (:mailbox row)))
            (get-in (root-state ctx) [:env :cleanup-cells])))))

(defn- mailbox-edit! [ctx w e f & args]
  (let [view (mailbox-view ctx {:w w :e e :allocation e} true)
        control (apply f (mailbox-control ctx w e) args)
        source (read-row ctx w :entities e)]
    (when (= :mailbox (:kind source)) (edit! ctx w :entities e assoc :mailbox control))
    (doseq [[key row] (get-in (root-state ctx) [:env :cleanup-cells])
            :when (and (= w (first key)) (= e (nth key 2 nil))
                       (= :mailbox (:kind row)) (= e (:allocation row)))]
      (root-edit! ctx assoc-in [:env :cleanup-cells key :mailbox] control))
    control))

(defn- mailbox-admit! [ctx {:keys [w op frame th cell callback] :as action} view]
  (require! view ::released-mailbox {:w w :cell cell})
  (let [ticket (when op (get-in (root-state ctx) [:env :native (first op)]))
        participant (when op (operation-row ctx op)) raw (get-in (root-state ctx) [:env :native callback])
        source (read-row ctx w :entities (:e action))
        thread (get-in (root-state ctx) [:env :threads th])
        held? (fn [receipt id]
                (and (:cell view) (contains? (:cells receipt #{}) (:cell view))
                     (contains? (:holders (:row view) #{}) id)))]
    (cond
      op (require! (and participant (= w (first (:owner ticket))) (contains? (:frames participant) frame)
                        (if (:cell view) (held? ticket (first op)) (not (cleanup-op? ticket))))
                   ::released-mailbox {:w w :op op :cell cell})
      callback (require! (and (= :mailbox-callback (:kind raw)) (= frame (:frame raw))
                              (= :executing (:phase raw)) (:physical? raw)
                              (= w (first (:owner raw)))
                              (if (:cell view) (held? raw callback)
                                  (and (not (:retired? raw)) (= :mailbox (:kind source))
                                       (= (:allocation action) (:allocation source)) (:owner source))))
                         ::released-mailbox {:callback callback :frame frame})
      (:run thread) (if (:cell view)
                      (let [n (:cleanup-ticket thread) cleanup (get-in (root-state ctx) [:env :native n])]
                        (require! (and (= w (:world thread)) (= :claimed (:phase cleanup)) (held? cleanup n))
                                  ::released-mailbox {:w w :cell cell :th th}))
                      (require! (and (= w (:world thread)) (not (:retired? thread))
                                     (not= :unwinding (:status (read-row ctx w :runs (:run thread)))))
                                ::cancelled {:w w :th th}))
      (:cell view) (require! (= :mailbox-post-request (:t action)) ::released-mailbox {:cell cell})
      :else nil)
    (when-not (:cell view) (deferred-admitted! ctx w))))

(defn- retain-mailbox! [ctx w e view holder]
  (let [key (or (:cell view) [w (:owner (:row view)) e])
        old (get-in (root-state ctx) [:env :cleanup-cells key])]
    (root-edit! ctx assoc-in [:env :cleanup-cells key]
                (assoc (or old {:kind :mailbox :allocation e :result nil :mailbox (:mailbox (:row view))})
                       :holders (conj (:holders old #{}) holder)))
    (root-edit! ctx update-in [:env :native holder :cells] (fnil conj #{}) key)
    key))

(defn- enqueue-mailbox-post! [ctx w e value message-id cell repost?]
  (let [sequence (inc (max (get (header ctx w) :seq 0) (get-in (root-state ctx) [:clocks w] 0)))
        envelope (cond-> {:mailbox-post e :allocation e :message-id (or message-id [e sequence])
                          :value value :seq sequence}
                   cell (assoc :cell cell) repost? (assoc :repost? true))]
    (root-edit! ctx assoc-in [:clocks w] sequence)
    (if (or (= :released (:status (header ctx w))) (= :fenced (:admission (header ctx w))))
      (root-edit! ctx update-in [:env :outside] (fnil conj []) {:w w :event envelope})
      (header-edit! ctx w update :queue (fnil conj []) envelope))))

(defn- create-mailbox! [ctx {:keys [w e allocation] :as action}]
  (deferred-admitted! ctx w)
  (require! (= e allocation) ::allocation-mismatch {:w w :e e :allocation allocation})
  (require! (nil? (read-row ctx w :entities e)) ::released-mailbox {:w w :e e})
  (create-source! ctx (assoc action :kind :mailbox :value nil))
  (edit! ctx w :entities e assoc :mailbox
         {:messages [] :consumers [] :pending {} :reservations {} :protected {} :physical {}}))

(defn- request-mailbox-post! [ctx {:keys [w e value cell message-id] :as action}]
  (let [view (mailbox-view ctx action true)]
    (mailbox-admit! ctx action view)
    (let [sequence (inc (max (get (header ctx w) :seq 0) (get-in (root-state ctx) [:clocks w] 0)))]
      (require! (or (nil? message-id) (= [e sequence] message-id))
                ::mailbox-message-mismatch {:message-id message-id}))
    (enqueue-mailbox-post! ctx w e value nil (:cell view) false)))

(defn- mailbox-select! [ctx w e message consumer]
  (let [control (mailbox-control ctx w e) pending (get-in control [:pending consumer])]
    (mailbox-edit! ctx w e
                   #(-> % (update :consumers (fn [ids] (vec (remove #{consumer} ids))))
                        (update :pending dissoc consumer)
                        (assoc-in [:reservations consumer]
                                  (assoc pending :message-id (:id message) :value (:value message) :state :reserved))
                        (cond-> (= :operation (:kind pending)) (update :protected dissoc (:reg pending)))))
    (case (:kind pending)
      :ordinary (edit! ctx w :runs (:r pending) assoc :status :running)
      :operation (root-edit! ctx update-in [:env :native (first (:op pending)) :operation :registrations (:reg pending)]
                             assoc :state :ready :delivery (:value message) :message-id (:id message))
      nil)))

(defn- process-mailbox-post! [ctx {:keys [w e allocation seq message-id cell] :as action}]
  (let [queued (first (:queue (header ctx w)))
        outside (when-not queued (first (filter #(= w (:w %)) (get-in (root-state ctx) [:env :outside]))))
        envelope (or queued (:event outside))]
    (require! (and (= e (:mailbox-post envelope)) (= allocation (:allocation envelope))
                   (= seq (:seq envelope)) (= message-id (:message-id envelope)) (= cell (:cell envelope)))
              ::not-mailbox-post {:w w :e e :envelope envelope})
    (let [view (or (mailbox-view ctx action true)
                   (mailbox-view ctx (dissoc action :cell) true))
          control (:mailbox (:row view)) selected (first (:consumers control))]
      (require! (or (not (contains? action :consumer)) (= selected (:consumer action)))
                ::not-mailbox-post {:consumer (:consumer action)})
      (if queued (header-edit! ctx w update :queue #(vec (rest %)))
          (root-edit! ctx update-in [:env :outside]
                      #(vec (remove (fn [held] (and (= w (:w held)) (= seq (get-in held [:event :seq])))) %))))
      (when view
        (let [message {:id message-id :value (:value envelope)}]
          (if selected (mailbox-select! ctx w e message selected)
              (mailbox-edit! ctx w e update :messages conj message))
          (emit! ctx {:event :mailbox-post :world w :e e :message-id message-id
                      :consumer selected :value (:value envelope)}))))))

(defn- detach-mailbox-consumer! [ctx w e consumer]
  (when-let [control (mailbox-control ctx w e)]
    (let [reservation (get-in control [:reservations consumer])
          key (when-not (:owner (read-row ctx w :entities e))
                (:cell (mailbox-view ctx {:w w :e e :allocation e} true)))]
      (mailbox-edit! ctx w e #(-> % (update :consumers (fn [ids] (vec (remove #{consumer} ids))))
                                  (update :pending dissoc consumer) (update :reservations dissoc consumer)
                                  (cond-> (= :operation (first consumer))
                                    (update :protected dissoc (second consumer)))))
      (when (= :reserved (:state reservation))
        (enqueue-mailbox-post! ctx w e (:value reservation) (:message-id reservation) key true)))))

(defn- mailbox-physical-claim! [ctx w e consumer kind frame view]
  (let [source (read-row ctx w :entities e)
        view (if (and (= :mailbox (:kind source)) (= e (:allocation source)) (:owner source))
               {:row source} view)
        owner (or (:owner (:row view)) (second (:cell view)))
        anchor (owner-chain ctx w owner)
        receipt [:mailbox-callback w owner consumer]]
    (root-edit! ctx assoc-in [:env :native receipt]
                {:kind :mailbox-callback :owner [w owner] :anchor anchor :state :running
                 :cells #{} :consumer consumer :consumer-kind kind :allocation e :frame frame :retired? false
                 :phase :executing :physical? true :variant :ok})
    (retain-mailbox! ctx w e view receipt)
    (mailbox-edit! ctx w e assoc-in [:physical frame]
                   {:consumer consumer :owner [w owner] :anchor anchor :kind kind})
    receipt))

(defn- queue-mailbox-rejection! [ctx w e consumer reason]
  (when-let [control (mailbox-control ctx w e)]
    (let [pending (get-in control [:pending consumer]) reservation (get-in control [:reservations consumer])
          target (or pending reservation)]
      (when (and (= :host (:kind target)) (not (#{:claimed :entered} (:state reservation))))
        (let [initial (mailbox-view ctx {:w w :e e :allocation e} true)]
          (detach-mailbox-consumer! ctx w e consumer)
          (let [view (or (mailbox-view ctx {:w w :e e :allocation e} true) initial)
                owner (or (:owner (:row view)) (second (:cell view)))
                anchor (owner-chain ctx w owner) frame [:mailbox-frame consumer]
                receipt [:mailbox-callback w owner consumer]]
            (root-edit! ctx assoc-in [:env :native receipt]
                        {:kind :mailbox-callback :owner [w owner] :anchor anchor :state :running
                         :cells #{} :consumer consumer :consumer-kind :host :allocation e :frame nil
                         :retired? false :phase :queued :physical? false :variant :error :delivery reason})
            (retain-mailbox! ctx w e view receipt)))))))

(defn- take-mailbox! [ctx {:keys [w e allocation consumer kind o r order available? th host callback] :or {order 0 host :caller} :as action}]
  (let [view (mailbox-view ctx action false)
        control (:mailbox (:row view))
        message (first (:messages control))
        expected [(if (= :ordinary kind) :obligation :host) o]]
    (mailbox-admit! ctx action view)
    (when callback
      (require! (and (not (:retired? (get-in (root-state ctx) [:env :native callback])))
                     (:owner (read-row ctx w :entities e)))
                ::cleanup-only {:callback callback}))
    (require! (and (#{:ordinary :host} kind)
                   (or (nil? callback) (= :host kind))
                   (= consumer expected) (= o [:o (get-in (root-state ctx) [:serial :o] 0)])
                   (or (not (contains? action :available?)) (= (boolean message) available?)))
              ::not-mailbox-consumer {:consumer consumer})
    (when (= :ordinary kind)
      (require! (and (= :running (:status (read-row ctx w :runs r)))
                     (= r (current-run ctx w (first r)))) ::not-running {:w w :r r})
      (when message
        (let [thread (get-in (root-state ctx) [:env :threads th])]
          (require! (and (:executing? thread) (= [w r] [(:world thread) (:run thread)]))
                    ::not-mailbox-frame {:th th :r r}))))
    (allocate! ctx :o)
    (add-obligation! ctx w o
                     (cond-> {:kind (if (= :ordinary kind) :await-once :deref)
                              :debtor [:entity w e] :creditor (if (= :ordinary kind) [:run w r] [:host host])
                              :standing? false :cont (when (= :ordinary kind) [:continuation o])
                              :token nil :order order :slot :armed}
                       (= :ordinary kind) (assoc :origin :created)
                       (= :host kind) (assoc :filter {:mode :local :origin w})))
    (let [pending (cond-> {:kind kind :o o :order order} (= :ordinary kind) (assoc :r r))]
      (if message
        (let [frame [:mailbox-frame consumer]]
          (mailbox-edit! ctx w e
                         #(-> % (update :messages (fn [messages] (vec (rest messages))))
                              (assoc-in [:reservations consumer]
                                        (assoc pending :message-id (:id message) :value (:value message)
                                               :state :claimed :frame frame))))
          (mailbox-physical-claim! ctx w e consumer kind frame view))
        (do (mailbox-edit! ctx w e #(-> % (update :consumers conj consumer) (assoc-in [:pending consumer] pending)))
            (when (= :ordinary kind) (edit! ctx w :runs r assoc :status :parked)))))
    (vreset! (:result ctx) {:available? (boolean message) :value (:value message)})))

(defn- claim-mailbox-success! [ctx {:keys [w e allocation consumer message-id frame th inline?] :as action}]
  (let [view (mailbox-view ctx action true)
        reservation (get-in (:mailbox (:row view)) [:reservations consumer])
        kind (:kind reservation) r (:r reservation)
        ticket (first (for [[n row] (get-in (root-state ctx) [:env :native])
                            :when (and (= :mailbox-callback (:kind row)) (= consumer (:consumer row))
                                       (= w (first (:owner row))) (= allocation (:allocation row)))] n))
        thread (get-in (root-state ctx) [:env :threads th])
        ob (read-row ctx w :obligations (:o reservation))]
    (require! (and view (#{:ordinary :host} kind) (= message-id (:message-id reservation)) (= frame [:mailbox-frame consumer])
                   (if inline? (and ticket (= :claimed (:state reservation)))
                       (and (= :reserved (:state reservation)) ob (= :armed (:slot ob))
                            (nil? ticket)
                            (if (= :ordinary kind) (= [:run w r] (:creditor ob))
                                (= :host (first (:creditor ob)))))))
              ::not-mailbox-reservation {:consumer consumer :message-id message-id})
    (when (= :ordinary kind)
      (require! (if inline?
                  (and (= w (:world thread)) (= r (:run thread)) (:executing? thread))
                  (and (= :running (:status (read-row ctx w :runs r))) (= r (current-run ctx w (first r)))
                       (nil? (:run thread))
                       (not-any? #(and (= w (:world %)) (= r (:run %)))
                                 (vals (get-in (root-state ctx) [:env :threads])))))
                ::not-mailbox-consumer {:w w :r r}))
    (when-not inline? (mailbox-physical-claim! ctx w e consumer kind frame view))
    (mailbox-edit! ctx w e update-in [:reservations consumer] assoc :state :entered :frame frame)
    (when (and (= :ordinary kind) (not inline?))
      (when (get-in (root-state ctx) [:model :cps-exit?])
        (edit! ctx w :runs r assoc :cps-entered? true))
      (root-edit! ctx update-in [:env :threads th] merge
                  {:world w :scope r :run r :obligation-world w :executing? true}))
    (end-obligation! ctx w (:o reservation) :delivered)
    (emit! ctx {:event :mailbox-entry :world w :e e :consumer consumer :message-id message-id
                :variant :ok :value (:value reservation)})
    (vreset! (:result ctx) {:value (:value reservation)})))

(defn- claim-mailbox! [ctx {:keys [w e allocation consumer frame callback variant] :as action}]
  (require! (or (nil? variant) (#{:ok :error} variant)) ::invalid-mailbox-variant {:variant variant})
  (if (= :error variant)
    (let [receipt (get-in (root-state ctx) [:env :native callback])
          control (mailbox-control ctx w e)]
      (require! (and (= e allocation (:allocation receipt)) (= :mailbox-callback (:kind receipt))
                     (= :queued (:phase receipt)) (false? (:physical? receipt)) (= :error (:variant receipt))
                     (= consumer (:consumer receipt)) (nil? (:frame receipt)) (= frame [:mailbox-frame consumer])
                     (= w (first (:owner receipt))) (not (contains? action :message-id)) control)
                ::not-mailbox-reservation {:consumer consumer :frame frame})
      (root-edit! ctx update-in [:env :native callback] assoc :phase :executing :physical? true :frame frame)
      (mailbox-edit! ctx w e assoc-in [:physical frame]
                     {:consumer consumer :owner (:owner receipt) :anchor (:anchor receipt) :kind :host})
      (emit! ctx {:event :mailbox-rejection-entry :world w :e e :consumer consumer
                  :variant :error :value (:delivery receipt)}))
    (claim-mailbox-success! ctx action)))

(defn- return-mailbox! [ctx {:keys [w e allocation consumer frame]}]
  (let [view (mailbox-view ctx {:w w :e e :allocation allocation} true)
        physical (get-in (:mailbox (:row view)) [:physical frame])
        receipt (first (for [[n row] (get-in (root-state ctx) [:env :native])
                             :when (and (= :mailbox-callback (:kind row)) (= consumer (:consumer row))
                                        (= frame (:frame row)) (= w (first (:owner row))) (= allocation (:allocation row)))] n))
        row (get-in (root-state ctx) [:env :native receipt])]
    (require! (and receipt view (= :executing (:phase row)) (:physical? row)
                   (= consumer (:consumer physical))
                   (or (= :error (:variant row))
                       (and (= :ok (:variant row))
                            (= :entered (get-in (:mailbox (:row view)) [:reservations consumer :state])))))
              ::not-mailbox-frame {:consumer consumer :frame frame})
    (mailbox-edit! ctx w e #(-> % (update :physical dissoc frame) (update :reservations dissoc consumer)))
    (release-cleanup-cells! ctx receipt)
    (root-edit! ctx update-in [:env :native] dissoc receipt)
    (let [[owner-world owner] (:owner row)]
      (when (and (= :unwinding (:status (read-row ctx owner-world :runs owner)))
                 (not (physical? ctx owner-world owner)))
        (remove-run! ctx owner-world owner)))))

(defn- take-mailbox-now! [ctx {:keys [w e r consumer-id available? message-id] :as action}]
  (let [view (mailbox-view ctx action false)
        consumer-node (when consumer-id (read-row ctx w :entities consumer-id))
        consumer-run (when consumer-id (current-run ctx w consumer-id))
        cancelled? (or (:cancelled-completion consumer-node)
                       (= :unwinding (:status (read-row ctx w :runs consumer-run))))
        admissible? (and (not cancelled?) (or (nil? r) (#{:running :parked} (:status (read-row ctx w :runs r)))))
        message (when admissible? (first (get-in view [:row :mailbox :messages])))]
    (mailbox-admit! ctx action view)
    (require! (or (not (contains? action :available?)) (= (boolean message) available?))
              ::mailbox-availability-mismatch {:available? available?})
    (when (contains? action :message-id)
      (require! (and message (= message-id (:id message))) ::mailbox-message-mismatch {:message-id message-id}))
    (when message
      (mailbox-edit! ctx w e update :messages #(vec (rest %)))
      (emit! ctx {:event :mailbox-immediate :world w :e e :message-id (:id message) :value (:value message)}))
    (vreset! (:result ctx) {:available? (boolean message) :value (:value message)})))

(defn- detach-mailbox! [ctx {:keys [w e allocation consumer]}]
  (require! (= e allocation) ::allocation-mismatch {:w w :e e})
  (let [control (mailbox-control ctx w e) pending (get-in control [:pending consumer])
        reservation (get-in control [:reservations consumer]) target (or pending reservation)]
    (require! (and control (or pending (= :reserved (:state reservation))))
              ::not-mailbox-consumer {:consumer consumer})
    (require! (:o target) ::not-mailbox-consumer {:consumer consumer})
    (end-obligation! ctx w (:o target) :creditor-cancelled)))

(defn- operation-await! [ctx {:keys [w op n sequence reg frame allocation e] :as action}]
  (let [participant (operation-frame! ctx action) ticket (get-in (root-state ctx) [:env :native n])
        source (read-row ctx w :entities e)
        mailbox? (or (= :mailbox (:kind source))
                     (= :mailbox (get-in (root-state ctx) [:env :cleanup-cells (:cell action) :kind])))
        live? (and (if mailbox? (= :mailbox (:kind source)) (= :deferred (:kind source)))
                   (= allocation (:allocation source)) (:owner source))
        view ((if mailbox? mailbox-view deferred-view) ctx
                                                       (if (get-in (root-state ctx) [:env :cleanup-cells (:cell action)]) action (dissoc action :cell)) false)
        row (:row view) key (or (:cell view) [w (:owner row) e])
        message (when mailbox? (first (get-in row [:mailbox :messages])))
        assigned? (if mailbox? (boolean message)
                      (if (:cell view) (get-in row [:deferred :assigned?]) (:completed? row)))]
    (require! (and view (= w (first (:owner ticket)))
                   (or (nil? (:cell action)) (= key (:cell action)))
                   (= reg [op (inc (:next-registration participant))]))
              ::not-operation-registration {:op op :reg reg})
    (if (:cell view)
      (require! (and (contains? (:cells ticket #{}) (:cell view)) (contains? (:holders row #{}) n))
                ::released-deferred {:cell (:cell view)})
      (deferred-admitted! ctx w))
    ((if mailbox? retain-mailbox! retain-deferred-for-ticket!) ctx w e view n)
    (root-edit! ctx update-in [:env :native n :operation :next-registration] inc)
    (root-edit! ctx assoc-in [:env :native n :operation :registrations reg]
                (cond-> {:w w :e e :allocation allocation :cell key
                         :state (if assigned? :claimed :pending) :continuation reg :entered? false}
                  assigned? (assoc :delivery (if mailbox? (:value message) (:result row)))
                  (and mailbox? assigned?) (assoc :message-id (:id message))))
    (if mailbox?
      (let [consumer [:operation reg] pending {:kind :operation :op op :reg reg :order (second reg)}]
        (if assigned?
          (mailbox-edit! ctx w e #(-> % (update :messages (fn [xs] (vec (rest xs))))
                                      (assoc-in [:reservations consumer]
                                                (assoc pending :message-id (:id message) :value (:value message)
                                                       :state :claimed :frame frame))))
          (mailbox-edit! ctx w e #(-> % (update :consumers conj consumer)
                                      (assoc-in [:pending consumer] pending)
                                      (assoc-in [:protected reg] {:operation op :sequence sequence})))))
      (when-not assigned?
        (deferred-edit! ctx w e view assoc-in [:deferred :protected reg] {:operation op :sequence sequence})))))

(defn- operation-deliver! [ctx {:keys [op reg value]}]
  (let [participant (operation-row ctx op) registration (get-in participant [:registrations reg])]
    (when (and (= :open (:state participant)) (= :pending (:state registration)))
      (let [{:keys [w e allocation cell]} registration]
        (when-let [view (or (deferred-retained ctx w e allocation cell)
                            (deferred-view ctx {:w w :e e :allocation allocation} false))]
          (deferred-edit! ctx w e view update-in [:deferred :protected] dissoc reg))
        (root-edit! ctx update-in [:env :native (first op) :operation :registrations reg]
                    assoc :state :ready :delivery value)))))

(defn- operation-claim! [ctx {:keys [op reg frame inline?]}]
  (let [participant (operation-row ctx op) registration (get-in participant [:registrations reg])
        ready (sort-by second (for [[id row] (:registrations participant) :when (= :ready (:state row))] id))]
    (require! (and (or (= :open (:state participant)) (and inline? (= :terminal (:state participant))))
                   registration (false? (:entered? registration))
                   (if inline?
                     (and (= :claimed (:state registration)) (contains? (:frames participant) frame))
                     (and (= :ready (:state registration)) (zero? (:physical participant))
                          (= reg (first ready)) (= frame [op (inc (:next-frame participant))]))))
              ::not-operation-ready {:op op :reg reg :frame frame})
    (when (contains? registration :message-id)
      (let [{:keys [w e]} registration
            consumer [:operation reg]
            reservation (get-in (mailbox-control ctx w e) [:reservations consumer])]
        (require! (and (= (:message-id registration) (:message-id reservation))
                       (= (if inline? :claimed :reserved) (:state reservation)))
                  ::not-mailbox-reservation {:consumer consumer})
        (mailbox-edit! ctx w e update-in [:reservations consumer] assoc :state :entered :frame frame)))
    (when-not inline?
      (root-edit! ctx update-in [:env :native (first op) :operation]
                  #(-> % (assoc :physical 1 :frames #{frame}) (update :next-frame inc))))
    (root-edit! ctx update-in [:env :native (first op) :operation :registrations reg]
                assoc :state :claimed :entered? true)
    (emit! ctx (cond-> {:event :continuation-entry :op op :reg reg :continuation reg
                        :variant :ok :value (:delivery registration)}
                 (contains? registration :message-id) (assoc :message-id (:message-id registration))))))

(defn- operation-terminal! [ctx {:keys [op n sequence value variant]}]
  (require! (#{:ok :error} variant) ::invalid-operation-variant {:op op :variant variant})
  (let [participant (operation-row ctx op) ticket (get-in (root-state ctx) [:env :native n])]
    (when (and (= n (first op)) (= sequence (second op) (:sequence ticket))
               (= :open (:state participant)))
      (doseq [[reg row] (:registrations participant) :when (not= :claimed (:state row))]
        (unlink-operation-registration! ctx op reg))
      (root-edit! ctx update-in [:env :native n :operation] assoc :state :terminal :variant variant)
      (root-edit! ctx update-in [:env :native n] assoc :phase :ready :delivery value)
      (emit! ctx {:event :operation-terminal :op op :variant variant :value value}))))

(defn- operation-return! [ctx {:keys [op frame reg inline?]}]
  (let [participant (operation-row ctx op)]
    (require! (and participant (contains? (:frames participant) frame)
                   (if reg (and (= :claimed (get-in participant [:registrations reg :state]))
                                (true? (get-in participant [:registrations reg :entered?])))
                       (and (not inline?) (= frame [op 1])))
                   (= 1 (:physical participant))
                   (or inline?
                       (not-any? (fn [[id row]] (and (not= id reg) (= :claimed (:state row))))
                                 (:registrations participant))))
              ::not-operation-return {:op op :frame frame :reg reg})
    (when reg (unlink-operation-registration! ctx op reg))
    (when-not inline?
      (root-edit! ctx update-in [:env :native (first op) :operation] assoc :physical 0 :frames #{}))))

(defn- create-deferred! [ctx {:keys [w e allocation] :as action}]
  (deferred-admitted! ctx w)
  (require! (= e allocation) ::allocation-mismatch {:w w :e e :allocation allocation})
  (require! (nil? (read-row ctx w :entities e))
            ::released-deferred {:w w :e e})
  (create-source! ctx (assoc action :kind :deferred :value nil))
  (edit! ctx w :entities e assoc :deferred {:claimed? false :protected {}}))

(defn- request-deferred! [ctx {:keys [w e allocation value claim? cell] :as action}]
  (let [view (deferred-view ctx action false)
        row (:row view)
        accepted? (or (not claim?) (not (get-in row [:deferred :claimed?])))]
    (admit-deferred-view! ctx action view)
    (when accepted?
      (when claim? (deferred-edit! ctx w e view assoc-in [:deferred :claimed?] true))
      (enqueue-deferred! ctx w (cond-> {:deferred-assignment e :allocation allocation :value value}
                                 cell (assoc :cell cell))))
    (vreset! (:result ctx) {:accepted? (boolean accepted?)})))

(defn- assign-deferred! [ctx {:keys [w e allocation cell seq] :as action}]
  (let [queued (first (:queue (header ctx w)))
        outside? (nil? queued)
        outside (when outside? (first (filter #(= w (:w %)) (get-in (root-state ctx) [:env :outside]))))
        event (or queued (:event outside))]
    (require! (and (= e (:deferred-assignment event)) (= allocation (:allocation event))
                   (= seq (:seq event)) (= cell (:cell event))
                   (or (not (contains? action :value)) (= (:value action) (:value event))))
              ::not-deferred-assignment {:w w :event event})
    (if outside?
      (root-edit! ctx update-in [:env :outside]
                  #(vec (remove (fn [held] (and (= w (:w held)) (= seq (get-in held [:event :seq])))) %)))
      (header-edit! ctx w update :queue #(vec (rest %))))
    ;; A committed envelope keeps its original cell evidence even if that
    ;; cohort ended. No caller admission is inferred from this resolution.
    (let [view (or (deferred-view ctx action true)
                   (deferred-view ctx (dissoc action :cell) true))
          row (:row view)
          assigned? (if (:cell view) (get-in row [:deferred :assigned?]) (:completed? row))]
      (when (and row (not assigned?))
        (let [protected (get-in row [:deferred :protected])
              metadata (assoc (:deferred row) :protected {})]
          (deferred-edit! ctx w e view
                          (fn [row]
                            (if (:cell view)
                              (assoc row :result (:value event) :deferred (assoc metadata :assigned? true))
                              (assoc row :result (:value event) :completed? true :deferred metadata))))
          (doseq [[reg edge] protected]
            (operation-deliver! ctx {:op (:operation edge) :reg reg :value (:value event)}))
          (when-not (:cell view)
            (doseq [v (conj (set (for [[x v d] (:fdeps (header ctx w))
                                       :when (if (= :bundle x) (contains? d e) (= x e))] v)) w)]
              (enqueue! ctx v {:completion e :debtor-world w :value (:value event)}))))))))

(defn- observe-deferred! [ctx {:keys [w e allocation host] :or {host :caller} :as action}]
  (let [{:keys [row] :as view} (deferred-view ctx action false)]
    (require! (and view (not (:cell view))) ::released-deferred {:w w :e e})
    (admit-deferred-view! ctx action view)
    (if (:completed? row)
      (do (emit! ctx {:event :host-delivery :world w :e e :value (:result row)})
          (vreset! (:result ctx) {:cached? true :value (:result row)}))
      (let [o (allocate! ctx :o)
            ob {:kind :deref :debtor [:entity w e] :creditor [:host host]
                :standing? false :cont nil :token nil :order 0 :slot :armed
                :filter {:mode :local :origin w}}]
        (add-obligation! ctx w o ob)
        (vreset! (:result ctx) {:o o :world w :cached? false :value nil})))))

(defn- protect-deferred! [_ctx action]
  (require! false ::obsolete-deferred-protection {:action action}))

(defn- allocate-generation! [ctx w e dense]
  (if-let [pending (:fresh-runs ctx)]
    (let [[world entity stamp :as witness] (first @pending)]
      (require! (and (vector? witness) (= 3 (count witness))
                     (= w world) (= e entity) (integer? stamp)
                     (> stamp (reduce max 0 (vals (:generation-clock (root-state ctx))))))
                ::invalid-run-allocation {:expected [w e] :witness witness})
      (vswap! pending next)
      stamp)
    dense))

(defn- start-run! [ctx w e scope cause]
  (require! (not (#{:deferred :mailbox} (:kind (read-row ctx w :entities e)))) ::not-computation {:w w :e e})
  (require! (= :live (:status (header ctx w))) ::sealed {:world w})
  (require! (open? ctx w scope) ::closed-scope {:world w :scope scope})
  (doseq [r (sort-by pr-str (read-row ctx w :runs-by-spin e))
          :when (= :inherited (:status (read-row ctx w :runs r)))]
    (cancel-run! ctx w r nil))
  (let [current (current-run ctx w e)
        pred (when-not (= :unwinding (:status (read-row ctx w :runs current))) current)
        n (allocate-generation! ctx w e (inc (max (or (second pred) 0)
                                                  (get-in (root-state ctx) [:generation-clock [w e]] 0))))
        r [e n]
        entry-reasons (when (:diagnostics? ctx) (reasons ctx w e))
        seqno (inc (max (get (header ctx w) :seq 0)
                        (get-in (root-state ctx) [:clocks w] 0)))]
    (root-edit! ctx assoc-in [:generation-clock [w e]] n)
    (header-edit! ctx w assoc :seq seqno)
    (edit! ctx w :entities e dissoc :cancelled-completion)
    (put! ctx w :runs r {:spin e :owner scope :pred pred
                         :ancestors (cond-> (get (read-row ctx w :runs pred) :ancestors #{}) pred (conj pred))
                         :status :running
                         :creations #{} :spawned #{} :seq seqno})
    (index-add! ctx w :runs-by-spin e r)
    (index-add! ctx w :runs-by-owner scope r)
    (when (read-row ctx w :runs scope)
      (edit! ctx w :runs scope update :spawned conj r))
    (when (:diagnostics? ctx)
      (emit! ctx {:event :body-entry :world w :e e :r r :cause cause
                  :completed? (:completed? (read-row ctx w :entities e))
                  :reasons entry-reasons
                  :reachable? (boolean
                               (some (fn [[_ h]] (and (= e (:spin h)) (:reachable? h)
                                                      (contains? (:touched h) w)))
                                     (get-in (root-state ctx) [:env :handles])))}))
    (command! ctx {:op :start :world w :spin e :run r})
    r))

(defn- move-run-owner! [ctx w r scope]
  (let [row (read-row ctx w :runs r)]
    (index-remove! ctx w :runs-by-owner (:owner row) r)
    (edit! ctx w :runs r assoc :owner scope)
    (index-add! ctx w :runs-by-owner scope r)))

(defn- adopt-call-target! [ctx w e scope]
  (let [er (read-row ctx w :entities e)
        previous (:owner er)
        lexical? (= previous (:creator er))]
    (when (and (= :spin (:kind er)) (predecessor? ctx w previous scope))
      (if lexical?
        (edit-entity! ctx w e assoc :owner scope :creator scope :kept? (reactive? ctx w scope))
        (edit-entity! ctx w e assoc :owner scope))
      (when lexical?
        (edit! ctx w :runs scope update :creations conj e))
      (doseq [r (sort-by pr-str (read-row ctx w :runs-by-spin e))
              :when (= previous (:owner (read-row ctx w :runs r)))]
        (move-run-owner! ctx w r scope)))))

(defn- create-spin! [ctx {:keys [w e tok order] :or {order 0} :as action}]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (let [scope (owner ctx w action)
        rr (read-row ctx w :runs scope)
        old (read-row ctx w :entities e)
        previous-creator (:creator old)
        adopt? (and rr old (predecessor? ctx w (:creator old) scope))
        h (get-in (root-state ctx) [:env :handles tok])]
    (require! (not (#{:deferred :mailbox} (:kind old))) ::not-computation {:w w :e e})
    (when h (require! (= e (:spin h)) ::token-spin-mismatch {:tok tok :e e :handle h}))
    (when (and tok (nil? h))
      (root-edit! ctx assoc-in [:env :handles tok]
                  {:spin e :reachable? true :touched #{} :dropped #{}}))
    (when (and rr (or (nil? old) adopt?))
      (if old
        (edit-entity! ctx w e assoc :owner scope :creator scope :kept? (reactive? ctx w scope) :order order)
        (put-entity! ctx w e (assoc (spin-row ctx w e scope)
                                    :owner scope :creator scope :kept? (reactive? ctx w scope) :order order)))
      (edit! ctx w :runs scope update :creations conj e))
    (when adopt?
      (doseq [r (sort-by pr-str (read-row ctx w :runs-by-spin e))
              :when (= previous-creator (:owner (read-row ctx w :runs r)))]
        (move-run-owner! ctx w r scope)))
    (touch! ctx w e tok)))

(defn- invalidate-computation! [ctx {:keys [w e]}]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (require! (and (= :open (:admission (header ctx w)))
                 (not-any? #(and (= w (:child %)) (= :attached (:phase %)))
                           (vals (:cuts (root-state ctx)))))
            ::not-admitted {:world w})
  (require! (= :spin (:kind (read-row ctx w :entities e))) ::not-computation {:w w :e e})
  (edit-entity! ctx w e assoc :dirty? true)
  (when-let [r (current-run ctx w e)]
    (edit! ctx w :runs r assoc :validation-lost? true)))

(defn- withdraw-deref! [ctx {:keys [w o]}]
  ;; Like unsubscribe, withdrawal is an ordinary boundary and cannot cross
  ;; a quiescent cut, including when the observer has already been served.
  (require! (not-any? #(and (= :p1q (:protocol %))
                            (#{:fenced :ready :captured :attached} (:phase %))
                            (contains? (get-in % [:participants :worlds]) w))
                      (vals (:cuts (root-state ctx))))
            ::not-admitted {:world w})
  (when-let [ob (read-row ctx w :obligations o)]
    (require! (= :open (:admission (header ctx w))) ::not-admitted {:world w})
    (require! (and (= :deref (:kind ob)) (not (:standing? ob))
                   (= :host (first (:creditor ob)))
                   (= :entity (first (:debtor ob))) (= w (second (:debtor ob))))
              ::not-host-deref {:w w :o o})
    (end-obligation! ctx w o :creditor-cancelled)))

(defn- publish-signal! [ctx {:keys [w e]}]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (require! (and (= :open (:admission (header ctx w)))
                 (not-any? #(and (= w (:child %)) (= :attached (:phase %)))
                           (vals (:cuts (root-state ctx))))) ::not-admitted {:world w})
  (let [source (read-row ctx w :entities e)]
    (require! (and (#{:signal :atom} (:kind source)) (:owner source)) ::released {:w w :e e})
    (doseq [v (conj (set (for [[x v d] (:fdeps (header ctx w))
                               :when (if (= :bundle x) (contains? d e) (= x e))] v)) w)]
      (enqueue! ctx v {:completion e :debtor-world w :value (:result source) :source-change? true}))))

(defn- cancel-computation! [ctx {:keys [w e tok value]}]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (require! (and (= :open (:admission (header ctx w)))
                 (not-any? #(and (= w (:child %)) (= :attached (:phase %)))
                           (vals (:cuts (root-state ctx))))) ::not-admitted {:world w})
  (let [handle (get-in (root-state ctx) [:env :handles tok]) old (read-row ctx w :entities e)]
    (require! (and handle (= e (:spin handle)) (:reachable? handle))
              ::unknown-handle {:w w :e e :tok tok})
    (require! (not (contains? (:dropped handle) w)) ::idle-cache-released {:w w :e e :tok tok})
    (require! (or (nil? old) (= :spin (:kind old))) ::not-computation {:w w :e e})
    (when-not old (put-entity! ctx w e (spin-row ctx w e (:root (header ctx w)))))
    (touch! ctx w e tok)
    (when-not (contains? (read-row ctx w :entities e) :cancelled-completion)
      (let [r (current-run ctx w e)
            dirty? (boolean (or (:dirty? (read-row ctx w :entities e))
                                (:validation-lost? (read-row ctx w :runs r))))
            targets (vec (sort-by second > (read-row ctx w :runs-by-spin e)))
            publication? (fn [event] (and (= e (:completion event)) (= w (:debtor-world event))))]
        (edit-entity! ctx w e assoc :completed? true :result value
                      :cancelled-completion {:run r :result value})
        (doseq [v (:known-worlds (root-state ctx))
                :when (some publication? (:queue (header ctx v)))]
          (header-edit! ctx v update :queue #(vec (remove publication? %))))
        (root-edit! ctx update-in [:env :outside]
                    #(vec (remove (fn [held] (publication? (:event held))) %)))
        (doseq [id targets]
          (retain-cleanup! ctx w id)
          (let [n (cleanup-ticket w id) ticket (get-in (root-state ctx) [:env :native n])]
            (when (and (cleanup-op? ticket) (not (contains? ticket :cancel-value)))
              (root-edit! ctx assoc-in [:env :native n :cancel-value] value))))
        (doseq [id targets] (cancel-run! ctx w id nil {:value value}))
        ;; Idle caches can still have incoming observers after their run left.
        (doseq [[v o] (sort-by #(second (second %))
                               (concat (map #(vector w %) (entity-obligations ctx w w e))
                                       (foreign-creditors ctx w e)))]
          (if (= v w)
            (let [ob (read-row ctx w :obligations o)]
              (when (= :run (first (:creditor ob))) (resume! ctx {:w w :o o :value value}))
              (end-obligation! ctx w o :cancel-delivered {:value value}))
            (cancel-foreign-debtor! ctx w v o {:value value})))
        (edit-entity! ctx w e assoc :dirty? dirty?)))))

(defn- reenter! [ctx {:keys [w e cause order resume-o] :or {cause :dirty order -1}}]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (let [r (current-run ctx w e)
        rr (read-row ctx w :runs r)]
    (require! rr ::missing-run {:e e})
    (doseq [p (sort-by pr-str (read-row ctx w :runs-by-spin e))
            :when (= :stale (:status (read-row ctx w :runs p)))]
      (supersede! ctx w p))
    (let [trigger (when resume-o (read-row ctx w :obligations resume-o))
          trigger (if (cells/row? trigger) (select-keys trigger [:kind :debtor :cont :order]) trigger)
          r2 (start-run! ctx w e (:owner rr) cause)
          previous (read-row ctx w :runs r)
          work? (#{:running :parked} (:status previous))]
      (when (and (#{:track :reactive} cause)
                 (or (:validation-lost? previous) (:dirty? (read-row ctx w :entities e))))
        (edit! ctx w :runs r2 assoc :validation-lost? true))
      (when trigger
        (vswap! (:commands ctx) update (dec (count @(:commands ctx)))
                assoc :op :reactive-resume :o resume-o :obligation trigger))
      (when work?
        (edit! ctx w :runs r assoc :status :stale))
      (doseq [o (read-row ctx w :by-run-creditor r)
              :let [ob (read-row ctx w :obligations o)]]
        (if (and previous
                 (or (and (= :track (:kind ob)) (<= (:order ob) order))
                     (and (= :await-reactive (:kind ob)) (:standing? ob)
                          (= :consumed (:slot ob)) (< (:order ob) order))))
          (do (index-remove! ctx w :by-run-creditor r o)
              (edit! ctx w :obligations o assoc :creditor [:run w r2])
              (index-add! ctx w :by-run-creditor r2 o)
              (let [[dk dw de] (:debtor ob)]
                (when (and (= :await-reactive (:kind ob)) (= :entity dk) (= w dw))
                  (adopt-call-target! ctx w de r2))))
          (when work? (end-obligation! ctx w o :creditor-cancelled))))
      (doseq [scope (read-row ctx w :scopes-by-parent r)
              :when (< (get (read-row ctx w :scopes scope) :order 0) order)]
        (index-remove! ctx w :scopes-by-parent r scope)
        (edit! ctx w :scopes scope assoc :parent r2)
        (index-add! ctx w :scopes-by-parent r2 scope))
      (doseq [k (get-in (root-state ctx) [:custody :by-holder (execution-holder w r)] #{})
              :let [cap (cap-row ctx k) acquisition (:holder-acquisition cap)]
              :when (and previous (integer? acquisition) (< acquisition order))]
        (put-cap! ctx k (assoc cap :holder (execution-holder w r2))))
      (doseq [child (:creations previous)
              :when (< (get (read-row ctx w :entities child) :order 0) order)]
        (if (:creator (read-row ctx w :entities child))
          (edit-entity! ctx w child assoc :owner r2 :creator r2)
          (edit-entity! ctx w child assoc :owner r2))
        (edit! ctx w :runs r2 update :creations conj child)
        (edit! ctx w :runs r update :creations disj child)
        (doseq [id (read-row ctx w :runs-by-spin child)
                :when (= r (:owner (read-row ctx w :runs id)))]
          (move-run-owner! ctx w id r2))))))

(defn- read-source [ctx w e]
  (cond (read-row ctx w :entities e) w
        (and (= :following (get-in (header ctx w) [:lineage :mode]))
             (get-in (header ctx w) [:lineage :parent]))
        (recur ctx (get-in (header ctx w) [:lineage :parent]) e)))

(defn- invoke! [ctx {:keys [w e tok mode host] :or {mode :deref host :caller} :as action}]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (let [scope (owner ctx w action)
        h (get-in (root-state ctx) [:env :handles tok])
        source (read-source ctx w e)
        _ (require! (not (#{:deferred :mailbox} (:kind (read-row ctx source :entities e))))
                    ::not-computation {:w w :e e})
        foreign? (and source (not= source w))
        foreign-run (current-run ctx source e)
        join? (and foreign? (or (#{:running :parked} (:status (read-row ctx source :runs foreign-run)))
                                (:completed? (read-row ctx source :entities e))))
        dw (if join? source w)]
    (require! (or (nil? tok) h) ::unknown-handle {:tok tok})
    (require! (not (contains? (:dropped h) w)) ::idle-cache-released {:w w :e e :tok tok})
    (require! (open? ctx w scope) ::closed-scope {:scope scope})
    (when (and (not join?) (nil? (read-row ctx w :entities e)))
      (put-entity! ctx w e (if foreign?
                             (assoc (read-row ctx source :entities e)
                                    :owner (:root (header ctx w)) :origin :copied :source-world source
                                    :tokens (:tokens (spin-row ctx w e scope)))
                             (spin-row ctx w e scope))))
    (when-not join?
      (adopt-call-target! ctx w e scope)
      (when (nil? (:owner (read-row ctx w :entities e)))
        (edit-entity! ctx w e assoc :owner scope))
      (touch! ctx dw e tok))
    (let [work (some #(when (#{:running :parked} (:status (read-row ctx dw :runs %))) %)
                     (read-row ctx dw :runs-by-spin e))
          er (read-row ctx dw :entities e)
          cached? (and (not work) (:completed? er) (or join? (not (:dirty? er))))]
      (when-not (or work cached?)
        (start-run! ctx w e scope (if (:dirty? er) :dirty :invoke)))
      (let [o (allocate! ctx :o)
            ob {:kind mode :debtor [:entity dw e] :creditor [:host host]
                :standing? (= mode :callback) :cont nil :token nil :order 0 :slot :armed
                :filter (get action :filter (get action :delivery-filter {:mode :local :origin w}))}]
        (if join?
          (enqueue! ctx dw {:register-host o :ob ob :tok tok :e e :caller-world w})
          (do
            (when cached? (emit! ctx {:event :host-delivery :world w :e e :o o}))
            (when (or (not cached?) (and (= mode :callback) (reactive? ctx dw (current-run ctx dw e))))
              (add-obligation! ctx dw o ob))))
        (vreset! (:result ctx) {:o o :world dw :cached? cached? :value (:result er)})))))

(defn- register! [ctx {:keys [w r kind debtor tok order recovery cont]
                       :or {order 0 recovery :retry}}]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (require! (= :running (:status (read-row ctx w :runs r))) ::not-running {:w w :r r})
  (let [h (get-in (root-state ctx) [:env :handles tok])]
    (require! (or (nil? tok) h) ::unknown-handle {:tok tok})
    (require! (not (contains? (:dropped h) w)) ::idle-cache-released {:w w :tok tok}))
  (let [[dk dw e] debtor
        _ (require! (or (not= :entity dk) (not= :mailbox (:kind (read-row ctx dw :entities e))))
                    ::unsupported-mailbox-obligation {:debtor debtor :kind kind})
        _ (require! (or (not= :entity dk)
                        (not= :deferred (:kind (read-row ctx dw :entities e)))
                        (= :await-once kind))
                    ::unsupported-deferred-obligation {:debtor debtor :kind kind})
        _ (when (and (= dk :entity) (= dw w)
                     (#{:await-once :await-reactive} kind)
                     (nil? (read-row ctx w :entities e)))
            (put-entity! ctx w e (spin-row ctx w e r)))
        _ (when (and (= dk :entity) (= dw w) (#{:await-once :await-reactive} kind)
                     (= :spin (:kind (read-row ctx w :entities e))))
            (adopt-call-target! ctx w e r))
        er (when (= dk :entity) (read-row ctx dw :entities e))
        await? (and (= dk :entity) (#{:await-once :await-reactive} kind))
        computation? (or (nil? er) (= :spin (:kind er)))
        _ (when (and await? computation? (= w dw) (nil? (:owner er)))
            (edit-entity! ctx dw e assoc :owner r))
        work? (some #(#{:running :parked} (:status (read-row ctx dw :runs %)))
                    (read-row ctx dw :runs-by-spin e))
        completed? (and (:completed? er)
                        (or (not= w dw) (and (not (:dirty? er)) (not work?))))
        foreign-cold? (and await? computation? (not= w dw) (not work?) (not (:completed? er)))]
    (require! (or (not= dk :entity) er foreign-cold?) ::missing-debtor {:debtor debtor})
    (when (and await? computation? (= w dw) (not work?) (not completed?))
      (start-run! ctx w e r (if (:dirty? er) :dirty :await)))
    (if (and (= kind :await-once) completed?)
      (do (when (:diagnostics? ctx) (emit! ctx {:event :inline-resume :world w :r r}))
          (vreset! (:result ctx) {:inline? true :value (:result er)}))
      (let [o (allocate! ctx :o)
            token [:cancel o]
            ob {:kind kind :debtor debtor :creditor [:run w r]
                :standing? (boolean (#{:track :await-reactive :callback} kind))
                :cont (or cont [:continuation o]) :token (when (= kind :external) token)
                :order order :origin :created
                :slot (if (= kind :track) :consumed :armed)}]
        (edit! ctx w :runs r assoc :status (if (= kind :track) :running :parked))
        (add-obligation! ctx w o ob)
        (if foreign-cold?
          (enqueue! ctx dw {:start-for e :creditor-world w :o o :tok tok})
          (add-fdep! ctx w o))
        (case kind
          :external
          (do (root-edit! ctx assoc-in [:env :waiters token]
                          {:world w :o o :registered? true :armed? false})
              (root-edit! ctx assoc-in [:env :native token]
                          {:owner [w r] :state :running :recovery recovery}))
          :timer
          (put-entity! ctx w [:timer o]
                       {:kind :timer :origin :created :owner r :creator nil
                        :completed? false :kept? false :result nil :tokens #{}
                        :key nil :order 0})
          (when-not foreign-cold? (touch! ctx dw e tok)))
        (let [immediate? (and (:immediate-await? ctx) (= kind :await-reactive) completed?)]
          (when immediate? (resume! ctx {:w w :o o :value (:result er) :direct? true}))
          (vreset! (:result ctx) {:o o :value (:result er) :inline? (boolean immediate?)}))))))

(defn- resume! [ctx {:keys [w o value direct? variant] :or {value :value}}]
  (when-let [ob (read-row ctx w :obligations o)]
    (let [[ck _ r] (:creditor ob)
          rr (read-row ctx w :runs r)]
      (when (and (= :armed (:slot ob)) (= ck :run) (= :inherited (:status rr)))
        (require! (= :live (:status (header ctx w))) ::not-live {:world w})
        (require! (= :open (:admission (header ctx w))) ::not-admitted {:world w}))
      (when (and (= :armed (:slot ob)) (= ck :run) (#{:parked :inherited} (:status rr)))
        (if (:standing? ob)
          (edit! ctx w :obligations o assoc :slot :consumed)
          (end-obligation! ctx w o :delivered))
        (edit! ctx w :runs r assoc :status :running)
        (doseq [id (read-row ctx w :by-run-creditor r)] (add-fdep! ctx w id))
        (doseq [dw (set (for [id (read-row ctx w :by-run-creditor r)
                              :let [[_ dw _] (:debtor (read-row ctx w :obligations id))]
                              :when (and dw (not= dw w))] dw))]
          (sync-bundle! ctx dw w))
        (doseq [id (read-row ctx w :by-run-creditor r)
                :let [other (read-row ctx w :obligations id)
                      [_ dw _] (:debtor other)
                      token [:cancel w id]]]
          (when (:dormant? other) (edit! ctx w :obligations id assoc :dormant? false))
          (case (:kind other)
            :timer (edit! ctx w :obligations id assoc :timer-armed? true)
            :external
            (do (edit! ctx w :obligations id assoc :token token)
                (root-edit! ctx assoc-in [:env :waiters token]
                            {:world w :o id :registered? true :armed? false})
                (root-edit! ctx assoc-in [:env :native token]
                            {:owner [w r] :state :running :recovery :retry}))
            nil))
        (when (:diagnostics? ctx)
          (emit! ctx {:event :resume :world w :r r :o o
                      :one-shot? (not (:standing? ob))
                      :thread-world w :value value}))
        (when-not direct?
          (command! ctx (cond-> {:op :resume :world w :run r :o o :cont (:cont ob) :value value}
                          variant (assoc :variant variant))))))))

(defn- register-timer! [ctx {:keys [w r o n th order delay-ms value] :or {order 0} :as action}]
  (let [thread (get-in (root-state ctx) [:env :threads th]) rr (read-row ctx w :runs r)
        expected [:o (get-in (root-state ctx) [:serial :o] 0)]]
    (require! (= :live (:status (header ctx w))) ::not-live {:world w})
    (require! (and (= :open (:admission (header ctx w))) (= :running (:status rr))
                   (= r (current-run ctx w (:spin rr))) (= [w r] [(:world thread) (:run thread)])
                   (:executing? thread) (nil? (:cleanup-ticket thread))
                   (not (protected-native? (get-in (root-state ctx) [:env :native (cleanup-ticket w r)])))
                   (nil? (:op action)) (nil? (:callback action)))
              ::not-timer-activation {:action action})
    (require! (and (= o expected) (= n [:timer w o]) (number? delay-ms)
                   (nil? (get-in (root-state ctx) [:env :native n])))
              ::not-timer-registration {:action action})
    (allocate! ctx :o)
    (add-obligation! ctx w o {:kind :timer :debtor [:host :executor] :creditor [:run w r]
                              :standing? false :cont [:continuation o] :token nil :order order
                              :origin :created :slot :armed :timer n})
    (edit! ctx w :runs r assoc :status :parked)
    (root-edit! ctx assoc-in [:env :native n]
                {:kind :timer-resource :owner [w r] :state :running :o o :order order
                 :delay-ms delay-ms :value value :phase :armed :install :pending :handle :none
                 :frames #{} :installer th :retired? false :anchor (owner-chain ctx w r)})))

(defn- settle-timer! [ctx n variant value]
  (let [{:keys [owner o]} (get-in (root-state ctx) [:env :native n]) [w r] owner]
    (root-edit! ctx update-in [:env :native n]
                #(cond-> (-> % (assoc :phase (if (= :ok variant) :fired :failed)) (dissoc :value))
                   (= :present (:handle %)) (assoc :handle :release-pending)))
    (resume! ctx {:w w :o o :value value :variant variant})))

(defn- install-timer-result! [ctx {:keys [w n variant handle? value] :as action}]
  (let [row (get-in (root-state ctx) [:env :native n])
        installer (get-in (root-state ctx) [:env :threads (:installer row)])]
    (require! (and (= :timer-resource (:kind row)) (= w (first (:owner row)))
                   (= :pending (:install row)) (= (:owner row) [(:world installer) (:run installer)])
                   (:executing? installer) (#{:ok :error} variant)
                   (or (true? handle?) (false? handle?))
                   (or (= :ok variant) (false? handle?)))
              ::not-timer-install {:action action})
    (let [armed? (= :armed (:phase row))]
      (root-edit! ctx update-in [:env :native n] assoc
                  :install (if (= :error variant) :failed (if handle? :seated :none))
                  :handle (if handle? (if armed? :present :release-pending) :none))
      (when (= :error variant)
        (if armed? (settle-timer! ctx n :error value)
            (emit! ctx {:event :timer-fault :world w :n n :stage :install :value value})))
      (prune-timer! ctx n))))

(defn- fire-timer! [ctx {:keys [w n frame variant value] :as action}]
  (let [{:keys [owner o phase] :as row} (get-in (root-state ctx) [:env :native n]) [_ r] owner
        ob (read-row ctx w :obligations o)]
    (require! (and (#{:ok :error} variant) (= frame [:timer-frame n 0]))
              ::not-timer-fire {:action action})
    (when (and (= :timer-resource (:kind row)) (= w (first owner)) (= :armed phase)
               (= :live (:status (header ctx w))) (= :open (:admission (header ctx w)))
               (= :parked (:status (read-row ctx w :runs r))) (= r (current-run ctx w (first r)))
               (= n (:timer ob)) (= :armed (:slot ob)))
      (require! (or (= :error variant) (= value (:value row))) ::not-timer-value {:action action})
      (root-edit! ctx assoc-in [:env :native n :frames] #{frame})
      (settle-timer! ctx n variant value)
      (emit! ctx {:event :timer-entry :world w :n n :r r :o o :frame frame
                  :variant variant :value value}))))

(defn- return-timer! [ctx {:keys [w n frame] :as action}]
  (let [row (get-in (root-state ctx) [:env :native n])]
    (require! (and (= :timer-resource (:kind row)) (= w (first (:owner row)))
                   (= #{frame} (:frames row)) (= frame [:timer-frame n 0]))
              ::not-timer-return {:action action})
    (root-edit! ctx assoc-in [:env :native n :frames] #{})
    (prune-timer! ctx n)))

(defn- release-timer-handle! [ctx {:keys [w n phase variant value] :as action}]
  (let [row (get-in (root-state ctx) [:env :native n])]
    (require! (and (= :timer-resource (:kind row)) (= w (first (:owner row)))
                   (not= :armed (:phase row))
                   (case phase :claim (= :release-pending (:handle row))
                         :returned (and (= :release-claimed (:handle row)) (#{:ok :error} variant)) false))
              ::not-timer-handle-release {:action action})
    (root-edit! ctx assoc-in [:env :native n :handle]
                (if (= :claim phase) :release-claimed (if (= :ok variant) :released :failed)))
    (when (and (= :returned phase) (= :error variant))
      (emit! ctx {:event :timer-fault :world w :n n :stage :release :value value}))
    (prune-timer! ctx n)))

(defn- refresh-timer-anchors! [ctx]
  (root-edit! ctx update-in [:env :native]
              #(into {} (for [[n row] %]
                          [n (if (and (= :timer-resource (:kind row)) (not (:retired? row)))
                               (assoc row :anchor (owner-chain ctx (first (:owner row)) (second (:owner row)))) row)]))))

(defn- complete! [ctx {:keys [w r value] :or {value :result}}]
  (let [rr (read-row ctx w :runs r)
        e (:spin rr)]
    (when (and (= :running (:status rr)) (= r (current-run ctx w e)))
      (edit! ctx w :entities e assoc :completed? true :dirty? (boolean (:validation-lost? rr)) :result value)
      (edit! ctx w :runs r assoc :status :completed)
      (enqueue! ctx w {:completion e :debtor-world w :value value})
      (doseq [v (set (for [[x v d] (:fdeps (header ctx w))
                           :when (if (= :bundle x) (contains? d e) (= x e))] v))]
        (enqueue! ctx v {:completion e :debtor-world w :value value}))
      (doseq [pred (sort-by pr-str (read-row ctx w :runs-by-spin e)) :when (not= r pred)]
        (when (#{:completed :stale} (:status (read-row ctx w :runs pred)))
          (supersede! ctx w pred)))
      (doseq [child (read-row ctx w :entities-by-owner r)
              :let [row (read-row ctx w :entities child)]
              :when (#{:timer :waiter} (:kind row))]
        (index-remove! ctx w :entities-by-owner r child)
        (delete! ctx w :entities child)))))

(defn- deliver! [ctx {:keys [w e debtor-world value]}]
  (require! (not (mailbox-control ctx (or debtor-world w) e)) ::unsupported-mailbox-publication {:w w :e e})
  ;; A foreign root loss can precede this world's next publication. Retire
  ;; unreachable completed creditors before a stale envelope can reenter them.
  (rule-l! ctx)
  (let [dw (or debtor-world w)
        ids (entity-obligations ctx w dw e)]
    (header-edit! ctx w update :queue
                  (fn [queue]
                    (let [[prefix remaining] (split-with #(not (and (= e (:completion %))
                                                                    (= dw (:debtor-world %)))) queue)]
                      (into (vec prefix) (rest remaining)))))
    (doseq [o ids :let [ob (read-row ctx w :obligations o)]]
      (if (= :host (first (:creditor ob)))
        (let [causal? (= :causal-follow (get-in ob [:filter :mode]))]
          (when-not (and causal? (contains? (:host-delivered (root-state ctx)) [w o]))
            (emit! ctx {:event :host-delivery :world w :e e :o o :value value :causal? causal?})
            (when causal? (root-edit! ctx update :host-delivered (fnil conj #{}) [w o])))
          (when (or (not (:standing? ob))
                    (and (:completed? (read-row ctx dw :entities e))
                         (not (reactive? ctx dw (current-run ctx dw e)))))
            (end-obligation! ctx w o :delivered)))
        (if (and (:standing? ob) (= :consumed (:slot ob))
                 (not= :inherited (:status (read-row ctx w :runs (nth (:creditor ob) 2)))))
          (reenter! ctx {:w w :e (first (nth (:creditor ob) 2))
                         :cause (if (= :track (:kind ob)) :track :reactive)
                         :order (:order ob) :resume-o o})
          (resume! ctx {:w w :o o :value value}))))))

(defn- fork-following! [ctx {:keys [w v k scope systems acceptance] :or {systems #{:a :b}}}]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (require! (not (or (some #(#{:deferred :mailbox} (:kind %)) (vals (store/table-view (:tx ctx) w :entities)))
                     (some (fn [[key row]] (and (= w (first key)) (#{:deferred :mailbox} (:kind row))))
                           (get-in (root-state ctx) [:env :cleanup-cells]))
                     (some (fn [[_ ticket]] (and (= w (first (:owner ticket)))
                                                 (or (:operation ticket) (= :timer-resource (:kind ticket)))))
                           (get-in (root-state ctx) [:env :native]))))
            ::unsupported-deferred-fork {:w w})
  (require! (open? ctx w scope) ::closed-scope {:scope scope})
  (let [acquisition (holder-acquisition! ctx w scope acceptance)
        _ (require! (not (contains? (:known-worlds (root-state ctx)) v)) ::world-id-reused {:world v})
        _ (fresh-cap! ctx k)
        copy-row #(assoc (cells/value %) :origin :inherited :source-world w)
        runs (into {} (for [[r rr] (store/table-view (:tx ctx) w :runs)
                            :when (= :parked (:status rr))]
                        [r (assoc (dissoc (copy-row rr) :cps-entered?) :status :inherited :owner [:root v])]))
        scopes (loop [parents (set (keys runs)) found {}]
                 (let [children (into {} (for [[id sr] (store/table-view (:tx ctx) w :scopes)
                                               :when (contains? parents (:parent sr))]
                                           [id (copy-row sr)]))]
                   (if (empty? children) found
                       (recur (set (keys children)) (merge found children)))))
        owners (into (set (keys runs)) (keys scopes))
        es (into (set (map :spin (vals runs)))
                 (for [[e er] (store/table-view (:tx ctx) w :entities)
                       :when (or (contains? owners (:owner er)) (contains? runs (:creator er)))] e))
        runs (into {} (for [[r rr] runs]
                        [r (-> rr (update :creations set/intersection es)
                               (update :spawned set/intersection (set (keys runs))))]))
        entities (into {} (for [e es :let [er (read-row ctx w :entities e)]]
                            [e (cond-> (assoc (copy-row er) :owner
                                              (if (contains? owners (:owner er)) (:owner er) [:root v]))
                                 (= :fork (:kind er)) (assoc :reference? true))]))
        obligations (into {} (for [[o ob] (store/table-view (:tx ctx) w :obligations)
                                   :when (or (contains? runs (nth (:creditor ob) 2 nil))
                                             (and (= :host (first (:creditor ob)))
                                                  (contains? es (nth (:debtor ob) 2 nil))
                                                  (= :causal-follow (get-in ob [:filter :mode]))))]
                               [o (cond-> (copy-row ob)
                                    (= :run (first (:creditor ob)))
                                    (assoc :creditor [:run v (nth (:creditor ob) 2)])
                                    (#{:timer :external} (:kind ob)) (assoc :token nil :dormant? true)
                                    (= :host (first (:creditor ob)))
                                    (assoc :cont nil :descriptor? true :debtor [:entity v (nth (:debtor ob) 2)]))]))
        evidence (into {} (for [[o ob] obligations]
                            [o {:phase (cond (cancelling? ctx w o) :cancelling
                                             (pending-start? ctx w o ob) :pending-start
                                             :else :admitted)
                                :cancelled (first (filter #(= o (:cancelled %)) (pending-events ctx w)))
                                :completions (vec (filter #(and (= (nth (:debtor ob) 2 nil) (:completion %))
                                                                (= (second (:debtor ob)) (get % :debtor-world w)))
                                                          (pending-events ctx w)))}]))
        events (distinct (sort-by :seq
                                  (mapcat (fn [[o ob]]
                                            (let [{:keys [cancelled completions]} (get evidence o)]
                                              (concat (when cancelled [cancelled])
                                                      (map #(assoc % :debtor-world (second (:debtor ob))) completions))))
                                          obligations)))
        queue (mapv #(assoc %1 :seq %2) events (range 1 (inc (count events))))
        child {:id v :lineage {:parent w :root (get-in (header ctx w) [:lineage :root])
                               :mode :following :cut nil :basis nil}
               :status :live :admission :open :seal-seq nil :root [:root v]
               :scopes (assoc scopes [:root v] {:kind :fork :parent nil :status :open})
               :next-scope (:next-scope (header ctx w)) :scope-balance (count scopes)
               :entities entities :runs runs :obligations obligations
               :releasing #{} :fdeps #{} :pins #{} :queue queue :seq (get (header ctx w) :seq 0)}
        last-seq (reduce max (:seq child) (keep :seq queue))
        cap {:world v :scope systems :holder (execution-holder w scope)
             :holder-acquisition acquisition
             :disposition :open :published? true :op nil :pred nil :successors []
             :bases (into {} (for [system systems] [system [:base v system]]))}]
    (doseq [[table rows] (encode-world child) [id row] rows]
      (put! ctx v table id row))
    (when (> last-seq (:seq child)) (root-edit! ctx assoc-in [:clocks v] last-seq))
    (root-edit! ctx update :generation-clock #(or % {}))
    (doseq [[r rr] runs]
      (root-edit! ctx update-in [:generation-clock [v (:spin rr)]] (fnil max 0) (second r)))
    (root-edit! ctx update :registry (fnil conj #{}) v)
    (root-edit! ctx update :known-worlds (fnil conj #{}) v)
    (root-edit! ctx assoc-in [:lineages v] (:lineage child))
    (put-entity! ctx w [:fork v] (entity-row :fork scope))
    (put-cap! ctx k cap)
    (doseq [[e er] entities]
      (when (= :spin (:kind er))
        (let [covering (set (for [[tok h] (get-in (root-state ctx) [:env :handles])
                                  :when (and (= e (:spin h)) (:reachable? h)
                                             (contains? (:touched h) v) (not (contains? (:dropped h) v)))] tok))]
          (edit! ctx v :entities e update :tokens set/union covering)))
      (doseq [tok (:tokens er)] (touch! ctx v e tok)))
    (doseq [[o ob] obligations
            :let [[kind dw e] (:debtor ob)]
            :when (and (= :entity kind) (not= dw v) (= :run (first (:creditor ob))))]
      (case (get-in evidence [o :phase])
        :cancelling nil
        :pending-start (enqueue! ctx dw {:start-for e :creditor-world v :o o})
        (add-fdep! ctx v o)))
    (vreset! (:result ctx) {:world v :cap k})))

(defn- start-request! [ctx w]
  (let [{e :start-for v :creditor-world o :o tok :tok :as event} (first (:queue (header ctx w)))
        ob (read-row ctx v :obligations o)
        pending? (and ob (= :armed (:slot ob)) (pending-start? ctx v o ob)
                      (not (cancelling? ctx v o))
                      (not (contains? (:fdeps (header ctx w)) [e v o]))
                      (not (some #(and (= :bundle (first %)) (= v (second %)) (contains? (nth % 2) e))
                                 (:fdeps (header ctx w)))))]
    (require! e ::not-start-request {:event event})
    (require! (not (#{:deferred :mailbox} (:kind (read-row ctx w :entities e)))) ::not-computation {:w w :e e})
    (header-edit! ctx w update :queue #(vec (rest %)))
    (when pending?
      (if (not= :live (:status (header ctx w)))
        (enqueue! ctx v {:cancelled o :value ::released})
        (let [owner (:root (header ctx w))]
          (when-not (read-row ctx w :entities e) (put-entity! ctx w e (spin-row ctx w e owner)))
          (let [er (read-row ctx w :entities e)
                completed? (:completed? er)
                value (:result er)]
            (when (and (= :spin (:kind er))
                       (not (or completed? (#{:running :parked} (:status (read-row ctx w :runs (current-run ctx w e)))))))
              (start-run! ctx w e owner :await))
            (touch! ctx w e tok)
            (add-fdep! ctx v o)
            (when completed? (enqueue! ctx v {:completion e :debtor-world w :value value}))))))))

(defn- cleanup! [ctx w]
  (when-not (= :released (:status (header ctx w)))
    (let [event (first (:queue (header ctx w)))]
      (require! event ::empty-queue {:w w})
      (header-edit! ctx w update :queue #(vec (rest %)))
      (cond
        (:fdep-ended event)
        (let [fd (:fdep-ended event)]
          (header-edit! ctx w update :releasing disj fd)
          (doseq [e (if (= :bundle (first fd)) (nth fd 2) [(first fd)])] (mark! ctx w e)))
        (:cancelled event) (let [delivery (assoc ctx :cancel-delivery [w (:cancelled event)])]
                             (resume! delivery {:w w :o (:cancelled event) :value (get event :value ::cancelled)})
                             (end-obligation! delivery w (:cancelled event) :cancel-delivered))
        (:fork-released event) (remove-entity! ctx w [:fork (:fork-released event)])
        :else (require! false ::not-cleanup {:event event})))))

(defn- release-id [w] [:world-release w])

(defn- cleanup-worlds [ctx w]
  (loop [pending [w] seen #{}]
    (if-let [world (peek pending)]
      (if (contains? seen world) (recur (pop pending) seen)
          (recur (into (pop pending)
                       (map :target-world (vals (get-in (root-state ctx) [:env :cleanup-targets world]))))
                 (conj seen world))) seen)))

(defn- cleanup-terminal? [ctx {:keys [target-world cap op]}]
  (let [state (root-state ctx)
        c (or (get-in state [:caps cap]) (get-in state [:durable :caps cap]))
        record (or (get-in state [:records op]) (get-in state [:durable :records op]))]
    (and (= target-world (:world c)) (= op (:op c)) (= cap (:cap record))
         (= op (:op record)) (= (:kind c) (:kind record))
         (= (:disposition c) (case (:kind record) :discard :discarded :merge :merged nil))
         (true? (:effects-released? record)) (every? #(= :done (:status %)) (:steps record)))))

(defn- composed-release-ready? [ctx w]
  (let [worlds (cleanup-worlds ctx w) env (:env (root-state ctx))]
    (and (every? (fn [world]
                   (and (= :released (:status (header ctx world)))
                        (not-any? #(and (= world (:world %)) (:run %)) (vals (:threads env)))
                        (not-any? #(and (= world (first (:owner %))) (not= :joined (:state %))) (vals (:native env)))))
                 worlds)
         (every? #(cleanup-terminal? ctx %)
                 (mapcat #(vals (get-in env [:cleanup-targets %])) worlds)))))

(defn- release-logical-profile? [ctx root required]
  (let [state (root-state ctx) worlds (:known-worlds state)
        same-family? #(= root (get-in state [:lineages % :root]))
        logical? (fn [world o ob]
                   (let [[kind dw e] (:debtor ob)]
                     (or (not= :entity kind) (= world dw)
                         (and (= [:run world] (subvec (vec (:creditor ob)) 0 2))
                              (#{:track :await-once :await-reactive} (:kind ob))
                              (same-family? world) (same-family? dw)
                              (or (#{:signal :atom :spin} (:kind (read-row ctx dw :entities e)))
                                  (and (= :released (:status (header ctx dw)))
                                       (cancelling? ctx world o ob)))))))
        involved? (fn [world ob] (or (contains? required world)
                                     (and (= :entity (first (:debtor ob)))
                                          (contains? required (second (:debtor ob))))))
        relevant (for [world worlds [o ob] (store/table-view (:tx ctx) world :obligations)
                       :when (involved? world ob)] [world o ob])
        endpoint-worlds (into required (mapcat (fn [[world _ ob]]
                                                 (cons world (when (= :entity (first (:debtor ob)))
                                                               [(second (:debtor ob))]))) relevant))]
    (and
     (every? (fn [[world o ob]]
               (and (or (not= :entity (first (:creditor ob))) (= world (second (:creditor ob))))
                    (logical? world o ob))) relevant)
     (not-any? #(and (#{:fenced :ready :captured :attached} (:phase %))
                     (seq (set/intersection endpoint-worlds (get-in % [:participants :worlds])))) (vals (:cuts state)))
     ;; Controls at an involved foreign endpoint are still outside this
     ;; bounded profile, even when that endpoint is outside cap/debt closure.
     (not-any? #(some % [:start-for :register-host])
               (mapcat (fn [world] (pending-events ctx world)) endpoint-worlds))
     (every? (fn [world]
               (let [row (header ctx world)
                     supported-entity? #(#{:signal :atom :spin} (:kind (read-row ctx world :entities %)))
                     dependency? (fn [[entity target members]]
                                   (and (same-family? target)
                                        (if (= :bundle entity) (every? supported-entity? members)
                                            (supported-entity? entity))))]
                 (and (every? dependency? (:fdeps row))
                      (every? dependency? (:releasing row))
                      (every? (fn [event]
                                (and (not (some event [:start-for :register-host]))
                                     (or (nil? (:join-bundle event))
                                         (and (same-family? (:join-bundle event))
                                              (every? #(and (same-family? (:source-world %))
                                                            (supported-entity? (:debtor %)))
                                                      (vals (:members event)))))))
                              (pending-events ctx world))))) required))))

(defn- local-release-profile! [ctx w]
  (let [state (root-state ctx) caps (merge (:caps state) (get-in state [:durable :caps]))
        terminal? #(#{:merged :discarded :transferred :partitioned} (:disposition %))
        root (get-in state [:lineages w :root])
        required (loop [pending [w] seen #{}]
                   (if-let [world (peek pending)]
                     (if (seen world) (recur (pop pending) seen)
                         (recur (into (pop pending)
                                      (concat (for [[_ c] caps
                                                    :when (and (not (terminal? c))
                                                               (= :execution-owner (first (:holder c)))
                                                               (= world (second (:holder c))))] (:world c))
                                              (map :target-world (vals (get-in state [:env :cleanup-targets world])))))
                                (conj seen world))) seen))
        supported? (fn [c]
                     (or (terminal? c)
                         (and (empty? (:scope c))
                              (= root (get-in state [:lineages (:world c) :root]))
                              (or (= :open (:disposition c))
                                  (and (= :discard (:kind c))
                                       (empty? (:steps (or (get-in state [:records (:op c)])
                                                           (get-in state [:durable :records (:op c)])))))))))]
    (require! (header ctx w) ::unknown-world {:w w})
    (require!
     (and
      (every? supported? (for [[_ c] caps
                               :when (and (= :execution-owner (first (:holder c)))
                                          (contains? required (second (:holder c))))] c))
      (every? supported? (for [world required [_ debt] (get-in state [:env :cleanup-targets world])]
                           (get caps (:cap debt))))
      (every? (fn [world]
                (let [row (header ctx world)]
                  (and row (= root (get-in state [:lineages world :root]))))) required)
      (release-logical-profile? ctx root required))
     ::unsupported-world-release {:w w})))

(def ^:private world-index-tables
  [:by-run-creditor :by-host-creditor :by-entity-creditor :by-local-debtor :by-foreign-debtor
   :by-debtor-world :runs-by-spin :runs-by-owner :spawned-by :created-by :entities-by-owner :scopes-by-parent])

(defn- release-world! [ctx {:keys [w]}]
  (when-let [world (header ctx w)]
    (when-not (= :released (:status world))
      (let [caps (filter #(= w (:world (val %))) (merge (:caps (root-state ctx)) (get-in (root-state ctx) [:durable :caps])))]
        (require! (not-any? #(#{:settling :incomplete} (:disposition (val %))) caps) ::settlement-open {:w w})
        (require! (or (nil? (get-in world [:lineage :parent]))
                      (every? #(#{:merged :discarded :transferred :partitioned} (:disposition (val %))) caps))
                  ::capability-open {:w w}))
      (local-release-profile! ctx w)
      (let [root (:root world) cancellation (:release-cancellation ctx)
            released-value (if cancellation (:value cancellation) ::released)
            raw-reason (if cancellation (:value cancellation) :org.replikativ.spindel.engine.protocols/released)]
        (retain-cleanup! ctx w root)
        (when cancellation
          (root-edit! ctx update-in [:env :native]
                      #(into {} (for [[id row] %]
                                  [id (if (and (= w (first (:owner row))) (cleanup-op? row)
                                               (not (contains? row :cancel-value)))
                                        (assoc row :cancel-value (:value cancellation)) row)]))))
        ;; Host results close before ordinary cancellation can replace release
        ;; with a debtor-cancel result. Raw errors retain a real callback lease.
        (doseq [[o ob] (store/table-view (:tx ctx) w :obligations)
                :when (= :host (first (:creditor ob)))]
          (let [[_ dw e] (:debtor ob) mailbox? (boolean (mailbox-control ctx dw e))]
            (when mailbox? (queue-mailbox-rejection! ctx w e [:host o] raw-reason))
            (end-obligation! ctx w o :creditor-cancelled)
            (when-not mailbox? (emit! ctx {:event :host-delivery :world w :o o :value released-value}))))
        ;; Dormant copies never entered this world; drop their links without
        ;; rejecting into another copy or manufacturing finalizer work.
        (doseq [[r rr] (store/table-view (:tx ctx) w :runs) :when (= :inherited (:status rr))]
          (doseq [o (read-row ctx w :by-run-creditor r)] (end-obligation! ctx w o :creditor-cancelled))
          (when (:diagnostics? ctx) (emit! ctx {:event :run-exit :world w :r r :cause :cancelled :t :t11}))
          (remove-run! ctx w r))
        (doseq [scope (sort-by pr-str (read-row ctx w :scopes-by-parent root))] (close-scope! ctx w scope))
        (doseq [r (sort-by pr-str (read-row ctx w :runs-by-owner root))] (cancel-run! ctx w r nil))
        (claim-owner-custody! ctx w root)
        (release-owned! ctx w root)
        ;; The debtor's admitted rows and queued requests authenticate foreign
        ;; creditors. Notify them before removing the world's routing tables.
        (doseq [v (:known-worlds (root-state ctx)) :when (not= w v)
                [o ob] (store/table-view (:tx ctx) v :obligations)
                :when (and (= [:entity w] (subvec (:debtor ob) 0 2))
                           (known-foreign-obligation? ctx w v o ob))]
          (enqueue! ctx v {:cancelled o}))
        (doseq [o (keys (store/table-view (:tx ctx) w :obligations))]
          (end-obligation! ctx w o :creditor-cancelled))
        (root-edit! ctx update-in [:env :threads]
                    #(into {} (for [[th row] %]
                                [th (cond-> row
                                      (and (= w (:world row)) (:run row))
                                      (assoc :anchor (owner-chain ctx w (:run row))))])))
        (root-edit! ctx update-in [:env :native]
                    #(into {} (for [[n row] %]
                                [n (cond-> row
                                     (and (= w (first (:owner row))) (not= :joined (:state row))
                                          (not= :mailbox-callback (:kind row)))
                                     (assoc :anchor (owner-chain ctx w (second (:owner row))))
                                     (and (= w (first (:owner row))) (= :mailbox-callback (:kind row)))
                                     (assoc :retired? true))])))
        (when-let [parent (get-in world [:lineage :parent])]
          (when (read-row ctx parent :entities [:fork w]) (enqueue! ctx parent {:fork-released w})))
        ;; Keep authenticated producer attempts in original world sequence;
        ;; preserve all other worlds' relative slots in the outside lane.
        (let [attempt? #(and (= w (:w %)) (or (:deferred-assignment (:event %)) (:mailbox-post (:event %))))
              held (into (vec (remove #(and (= w (:w %)) (not (attempt? %)))
                                      (get-in (root-state ctx) [:env :outside])))
                         (for [event (:queue (header ctx w)) :when (or (:deferred-assignment event) (:mailbox-post event))]
                           {:w w :event event}))
              attempts (sort-by #(get-in % [:event :seq]) (filter attempt? held))
              ordered (loop [remaining held attempts attempts result []]
                        (if-let [next (first remaining)]
                          (if (attempt? next)
                            (recur (rest remaining) (rest attempts) (conj result (first attempts)))
                            (recur (rest remaining) attempts (conj result next))) result))]
          (root-edit! ctx assoc-in [:env :outside] ordered))
        (doseq [table (concat world-tables world-index-tables)
                id (keys (store/table-view (:tx ctx) w table))]
          (store/delete-row! (:tx ctx) w table id))
        ;; The header's run-creation clock disappears with the tombstone;
        ;; retained producer attempts must still advance past every old ID.
        (root-edit! ctx assoc-in [:clocks w]
                    (max (get (header ctx w) :seq 0) (get-in (root-state ctx) [:clocks w] 0)))
        (put! ctx w :header :world (assoc (select-keys world [:id :lineage]) :status :released))
        (root-edit! ctx update :registry disj w)))))

(defn- release-row! [ctx {:keys [w release] :as action}]
  (let [row (get-in (root-state ctx) [:env :releases w])]
    (require! (and (= release (release-id w)) (= release (:id row)))
              ::invalid-release-receipt {:action action}) row))

(defn- release-caller-worlds! [ctx {:keys [caller-th th op frame callback] :as action}]
  (require! (nil? th) ::invalid-release-caller {:action action})
  (let [state (root-state ctx) thread (get-in state [:env :threads caller-th])
        operation (when (some? op) (operation-row ctx op)) ticket (when (vector? op) (get-in state [:env :native (first op)]))
        raw (get-in state [:env :native callback])
        control (when (some? callback) (mailbox-control ctx (first (:owner raw)) (:allocation raw)))
        reservation (get-in control [:reservations (:consumer raw)])]
    (when (some? caller-th)
      (require! (and thread (:world thread) (or (nil? (:run thread)) (:executing? thread)))
                ::invalid-release-caller {:action action}))
    (when (some? op)
      (require! (and operation (protected-native? ticket) (= (second op) (:sequence ticket))
                     (contains? (:frames operation) frame)) ::invalid-release-caller {:action action}))
    (when (some? callback)
      (require! (and (= :mailbox-callback (:kind raw)) (= frame (:frame raw))
                     (= :executing (:phase raw)) (:physical? raw)
                     (or (= :error (:variant raw))
                         (and (= :ok (:variant raw)) (= :entered (:state reservation))
                              (= frame (:frame reservation)))))
                ::invalid-release-caller {:action action}))
    (require! (or (nil? frame) op callback) ::invalid-release-caller {:action action})
    (set (concat (when (:run thread) [(:world thread)])
                 (when (some? op) [(first (:owner ticket))]) (when (some? callback) [(first (:owner raw))])))))

(defn- request-release! [ctx {:keys [w release caller-th op callback] :as action}]
  (release-caller-worlds! ctx action)
  (require! (and (nil? op) (nil? callback)) ::cleanup-only {:action action})
  (let [thread (get-in (root-state ctx) [:env :threads caller-th])]
    (when-let [r (:run thread)]
      (require! (and (nil? (:cleanup-ticket thread)) (not (:retired? thread))
                     (not= :unwinding (:status (read-row ctx (:world thread) :runs r))))
                ::cleanup-only {:action action})))
  (when-not (get-in (root-state ctx) [:env :releases w]) (local-release-profile! ctx w))
  (require! (= release (release-id w)) ::invalid-release-receipt {:action action})
  (if (get-in (root-state ctx) [:env :releases w])
    (release-row! ctx action)
    (let [reason (get action :reason :org.replikativ.spindel.engine.protocols/released)]
      (root-edit! ctx assoc-in [:env :releases w]
                  {:id release :reason reason :phase :releasing :next-observer 0 :observers {}})
      (release-world! (assoc ctx :release-cancellation {:value reason}) action)))
  (vreset! (:result ctx) {:release release}))

(defn- observe-release! [ctx {:keys [w release observer] :as action}]
  (let [row (release-row! ctx action) callers (release-caller-worlds! ctx action)]
    (require! (not-any? (cleanup-worlds ctx w) callers) ::release-self-join {:action action})
    (require! (= observer [release (inc (:next-observer row))]) ::not-release-observer {:action action})
    (root-edit! ctx update-in [:env :releases w :next-observer] inc)
    (root-edit! ctx assoc-in [:env :releases w :observers observer]
                {:state (if (= :joined (:phase row)) :ready :waiting)})
    (when (= :joined (:phase row)) (command! ctx {:op :release-ready :world w :release release :observer observer}))
    (vreset! (:result ctx) {:observer observer})))

(defn- detach-release! [ctx {:keys [w observer] :as action}]
  (let [row (release-row! ctx action)]
    (release-caller-worlds! ctx action)
    (require! (and (vector? observer) (= 2 (count observer)) (= (:id row) (first observer))
                   (integer? (second observer)) (<= 1 (second observer) (:next-observer row)))
              ::not-release-observer {:action action})
    (root-edit! ctx update-in [:env :releases w :observers] dissoc observer)))

(defn- notify-release! [ctx {:keys [w release observer] :as action}]
  (let [row (release-row! ctx action)]
    (require! (not-any? #(some? (get action %)) [:th :caller-th :op :frame :callback])
              ::invalid-release-caller {:action action})
    (require! (and (= :joined (:phase row)) (= :ready (get-in row [:observers observer :state])))
              ::not-release-ready {:action action})
    (root-edit! ctx update-in [:env :releases w :observers] dissoc observer)
    (emit! ctx {:event :release-delivery :world w :release release :observer observer :variant :ok :value nil})
    (command! ctx {:op :release-delivery :world w :release release :observer observer :variant :ok :value nil})))

(defn- stale-release-producer? [ctx w {:keys [event] :as packet}]
  (let [kind (cond (contains? event :deferred-assignment) :deferred
                   (contains? event :mailbox-post) :mailbox)
        e (get event (case kind :deferred :deferred-assignment :mailbox :mailbox-post nil))
        allocation (:allocation event) source (read-row ctx w :entities e)]
    (and (= w (:w packet)) kind (contains? event :allocation)
         (= :released (:status (header ctx w)))
         (not (and (= kind (:kind source)) (= allocation (:allocation source)) (:owner source)))
         (not-any? (fn [[key cell]]
                     (and (= w (first key)) (= e (nth key 2 nil))
                          (= kind (:kind cell)) (= allocation (:allocation cell)) (seq (:holders cell))))
                   (get-in (root-state ctx) [:env :cleanup-cells])))))

(defn- refresh-releases! [ctx]
  (let [ready (set (filter #(composed-release-ready? ctx %) (:known-worlds (root-state ctx))))
        debts (get-in (root-state ctx) [:env :cleanup-targets])]
    (when (seq debts)
      (let [remaining (into {} (keep (fn [[w rows]]
                                       (let [rows (into {} (remove (fn [[_ debt]]
                                                                     (and (contains? ready (:target-world debt))
                                                                          (cleanup-terminal? ctx debt))) rows))]
                                         (when (seq rows) [w rows]))) debts))]
        (if (seq remaining) (root-edit! ctx assoc-in [:env :cleanup-targets] remaining)
            (root-edit! ctx update :env dissoc :cleanup-targets))))
    (doseq [[w row] (get-in (root-state ctx) [:env :releases])
            :when (and (= :releasing (:phase row)) (contains? ready w))]
      (root-edit! ctx update-in [:env :outside]
                  #(vec (remove (partial stale-release-producer? ctx w) %)))
      (root-edit! ctx update-in [:env :releases w]
                  #(-> % (assoc :phase :joined :result nil)
                       (update :observers (fn [observers]
                                            (into {} (for [[id observer] observers] [id (assoc observer :state :ready)]))))))
      (emit! ctx {:event :release-joined :world w :release (:id row)})
      (doseq [observer (keys (:observers row))]
        (command! ctx {:op :release-ready :world w :release (:id row) :observer observer})))))

(defn- admit-action!
  "Check actor/resource admission before any transition mutates the store."
  [ctx {:keys [t w] :as action} thread slice? unwinding?]
  (when (#{:t20 :t20q} t)
    (let [worlds (get-in action [:participants :worlds]) state (root-state ctx)]
      (when (some #(and (= :timer-resource (:kind %)) (contains? worlds (first (:owner %))))
                  (vals (get-in state [:env :native])))
        (require! false ::unsupported-timer-cut {:action action}))
      (when (or (some (fn [world] (some #(#{:deferred :mailbox} (:kind %))
                                        (vals (store/table-view (:tx ctx) world :entities)))) worlds)
                (some (fn [[key row]] (and (contains? worlds (first key)) (#{:deferred :mailbox} (:kind row))))
                      (get-in state [:env :cleanup-cells]))
                (some #(and (contains? worlds (first (:owner %)))
                            (or (:operation %) (= :mailbox-callback (:kind %))))
                      (vals (get-in state [:env :native]))))
        (require! false ::unsupported-resource-cut {:action action}))))
  (when (contains? action :fresh-runs)
    (require! (and (vector? (:fresh-runs action))
                   (every? #(and (vector? %) (= 3 (count %))) (:fresh-runs action)))
              ::invalid-run-allocation {:action action}))
  (when (and slice? (not (#{:t38 :cleanup-adopt :cleanup-park :cleanup-return :cleanup-cell :deferred-request :mailbox-post-request :mailbox-take-now :mailbox-claim :mailbox-return :operation-start :operation-await :operation-deliver :operation-claim :operation-terminal :operation-return} t)) (= :released (:status (header ctx (:world thread)))))
    (require! false ::released {:w w :thread (:th action)}))
  (when (and unwinding? (#{:t01 :t02 :t03 :t04 :t05 :t12 :t19 :t20 :t20q
                           :invalidate-computation :withdraw-deref :cancel-computation :signal-publish :deferred-create :deferred-observe :mailbox-create :mailbox-take :timer-register} t))
    (require! false ::cancelled {:w w :r (:run thread)}))
  (when (and (or (:cleanup-ticket thread)
                 (cleanup-op? (get-in (root-state ctx) [:env :native (cleanup-ticket (:world thread) (:run thread))])))
             (not (#{:t38 :cleanup-adopt :cleanup-park :cleanup-return :cleanup-cell :deferred-request :mailbox-post-request :mailbox-take-now :mailbox-claim :mailbox-return :operation-start :operation-await :operation-deliver :operation-claim :operation-terminal :operation-return} t)))
    (require! false ::cleanup-only {:thread (:th action) :action action}))
  (when (and (protected-operation-id? (:op action))
             (not (#{:operation-start :operation-await :operation-deliver :operation-claim
                     :operation-terminal :operation-return :cleanup-cell :deferred-request :mailbox-post-request :mailbox-take-now :signal-write :release-observe :release-detach} t)))
    (require! false ::cleanup-only {:action action}))
  (when (:callback action)
    (let [receipt (get-in (root-state ctx) [:env :native (:callback action)])
          reservation (get-in (mailbox-control ctx (first (:owner receipt)) (:allocation receipt))
                              [:reservations (:consumer receipt)])]
      (require! (and (= :mailbox-callback (:kind receipt)) (or (= (:frame action) (:frame receipt))
                                                               (and (= :mailbox-claim t) (= :error (:variant action))
                                                                    (= :queued (:phase receipt)) (nil? (:frame receipt))
                                                                    (= (:frame action) [:mailbox-frame (:consumer receipt)])))
                     (= w (first (:owner receipt)))
                     (or (= :mailbox-claim t)
                         (and (= :executing (:phase receipt)) (:physical? receipt)
                              (or (= :error (:variant receipt))
                                  (and (= :ok (:variant receipt)) (= :entered (:state reservation))
                                       (= (:frame receipt) (:frame reservation))))))
                     (#{:cleanup-cell :deferred-request :mailbox-post-request :mailbox-take-now
                        :mailbox-take :mailbox-claim :mailbox-return :release-observe :release-detach} t))
                ::cleanup-only {:action action})))
  (let [resume (case t :t06 action :t35 (when (= :resume (get-in action [:op :kind])) (:op action)) nil)
        ob (when resume (read-row ctx (:w resume) :obligations (:o resume)))
        [_ dw e] (:debtor ob)]
    (when (:timer ob)
      (require! false ::unsupported-timer-resume {:action action}))
    (when (and ob (mailbox-control ctx dw e))
      (require! false ::unsupported-mailbox-resume {:action action}))))

(defn- observe-join [ctx {:keys [w x timeout?]}]
  (let [released? (= :released (:status (header ctx w)))
        env (:env (root-state ctx))
        under? (fn [r participant]
                 (if (or released? (= :mailbox-callback (:kind participant)))
                   (or (= x w) (= x r) (some #{x} (:anchor participant)))
                   (some #{x} (owner-chain ctx w r))))
        busy (vec
              (distinct
               (concat
                (when-not released?
                  (for [[r rr] (store/table-view (:tx ctx) w :runs)
                        :when (and (#{:running :parked :unwinding} (:status rr))
                                   (some #{x} (owner-chain ctx w r)))] r))
                (for [[_ thread] (:threads env)
                      :let [r (:run thread)]
                      :when (and r (= w (:world thread)) (under? r thread))] r)
                (for [[_ native] (:native env)
                      :let [[world r] (:owner native)]
                      :when (and (= w world) (not= :joined (:state native))
                                 (under? r native))] r))))]
    (require! (not (and timeout? (seq busy))) ::join-timeout {:w w :x x :busy busy})
    {:complete? (empty? busy) :busy busy}))

(defn step!
  "Execute a supported transition, returning delivery descriptors after commit.
  Unsupported actions refuse explicitly; this is not yet the runtime engine."
  [kernel {:keys [t w o] :as action}]
  (if (= :join t)
    ;; Observation bypasses admission, normalization and event replacement.
    (store/transact! kernel
                     (fn [tx]
                       {:events [] :commands []
                        :result (observe-join {:tx tx} action)}))
    (store/transact!
     kernel
     (fn [tx]
       (let [process-live? (:process-live? (read-row {:tx tx} environment :state :root))]
         (require! (boolean? process-live?) ::invalid-process-state {:process-live? process-live?})
         (require! (or process-live? (= :t31 t)) ::process-lost {:action action}))
       (let [diagnostics? (get (store/options kernel) :diagnostics? true)
             ctx {:tx tx :events (when diagnostics? (volatile! [])) :work (volatile! [])
                  :work-set (volatile! #{}) :retiring-owners (volatile! {})
                  :commands (volatile! []) :result (volatile! nil)
                  :fresh-runs (when (contains? action :fresh-runs) (volatile! (:fresh-runs action)))
                  :diagnostics? diagnostics? :immediate-await? (= t :await)
                  :cache-gc-only? (= t :t17)}
             thread (get-in (root-state ctx) [:env :threads (:th action)])
             slice? (:run thread)
             unwinding? (= :unwinding (:status (read-row ctx (:world thread) :runs (:run thread))))
             action (if (and slice? (not (#{:t38 :slice-enter :t35} t)))
                      (assoc action :w (:world thread)) action)
             w (:w action)
             ctx (assoc ctx :acting-world w)]
         (admit-action! ctx action thread slice? unwinding?)
         (case t
           :finalization-wait (finalization-wait! ctx action)
           :finalization-resume (finalization-resume! ctx action)
           :cleanup-adopt (cleanup-adopt! ctx action)
           :cleanup-claim (cleanup-claim! ctx action)
           :cleanup-park (cleanup-boundary! ctx action :waiting)
           :cleanup-return (cleanup-boundary! ctx action :returning)
           :cleanup-deliver (cleanup-deliver! ctx action)
           :cleanup-cell (cleanup-access! ctx action)
           :source-unreachable (source-unreachable! ctx action)
           :reap-source (reap-source! ctx action)
           :invalidate-computation (invalidate-computation! ctx action)
           :withdraw-deref (withdraw-deref! ctx action)
           :cancel-computation (cancel-computation! ctx action)
           :signal-publish (publish-signal! ctx action)
           :deferred-create (create-deferred! ctx action)
           :deferred-request (request-deferred! ctx action)
           :deferred-assign (assign-deferred! ctx action)
           :deferred-observe (observe-deferred! ctx action)
           :deferred-protect (protect-deferred! ctx action)
           :mailbox-create (create-mailbox! ctx action)
           :mailbox-post-request (request-mailbox-post! ctx action)
           :mailbox-post (process-mailbox-post! ctx action)
           :mailbox-take (take-mailbox! ctx action)
           :mailbox-take-now (take-mailbox-now! ctx action)
           :mailbox-claim (claim-mailbox! ctx action)
           :mailbox-detach (detach-mailbox! ctx action)
           :mailbox-return (return-mailbox! ctx action)
           :operation-start (operation-start! ctx action)
           :operation-await (operation-await! ctx action)
           :operation-deliver
           (require! false ::unsupported-operation-delivery {:action action})
           :operation-claim (operation-claim! ctx action)
           :operation-terminal (operation-terminal! ctx action)
           :operation-return (operation-return! ctx action)
           :arrival
           (let [event (:event action)]
             (if (:deferred-assignment event)
               (assign-deferred! ctx (assoc event :w w :e (:deferred-assignment event)))
               (if (:mailbox-post event)
                 (process-mailbox-post! ctx (assoc event :w w :e (:mailbox-post event)))
                 (throw (ex-info "Unsupported kernel transition" {:action action})))))
           :t01 (create-spin! ctx action)
           :t02
           (do (require! (not (#{:deferred :mailbox} (:kind action))) ::reserved-source-kind {:kind (:kind action)})
               (create-source! ctx action))
           :t04 (invoke! ctx action)
           :t03
           (let [r (:r action)
                 rr (read-row ctx w :runs r)]
             (require! (#{:running :parked} (:status rr)) ::not-work {:r r})
             (require! (not (#{:deferred :mailbox} (:kind action))) ::reserved-source-kind {:kind (:kind action)})
             (let [e [(:spin rr) (:key action)]]
               (require! (not (#{:deferred :mailbox} (:kind (read-row ctx w :entities e))))
                         ::reserved-source-kind {:w w :e e})
               (put-entity! ctx w e
                            (assoc (entity-row (get action :kind :cache-row) r)
                                   :order (get action :order 0)))
               (edit! ctx w :runs r update :creations conj e)))
           :t12
           (do (require! (= :live (:status (header ctx w))) ::not-live {:world w})
               (let [scope (:scope action)]
                 (require! (and (vector? scope) (= 3 (count scope))
                                (= [:scope :id] (subvec scope 0 2))
                                (integer? (nth scope 2)) (not (neg? (nth scope 2))))
                           ::invalid-scope-id {:scope scope})
                 (require! (and (>= (nth scope 2) (:next-scope (header ctx w)))
                                (nil? (read-row ctx w :scopes scope))
                                (not= scope (:parent action))) ::scope-id-reused {:scope scope}))
               (require! (open? ctx w (:parent action)) ::closed-scope {:parent (:parent action)})
               (header-edit! ctx w assoc :next-scope (inc (nth (:scope action) 2)))
               (header-edit! ctx w update :scope-balance inc)
               (put! ctx w :scopes (:scope action)
                     (cond-> {:kind (get action :kind :explicit) :parent (:parent action) :status :open}
                       (read-row ctx w :runs (:parent action)) (assoc :order (get action :order 0))))
               (index-add! ctx w :scopes-by-parent (:parent action) (:scope action)))
           :timer-register (register-timer! ctx action)
           :timer-install-result (install-timer-result! ctx action)
           :timer-fire (fire-timer! ctx action)
           :timer-return (return-timer! ctx action)
           :timer-handle-release (release-timer-handle! ctx action)
           :t05 (register! ctx action)
         ;; The gate excludes observation between registration and claim.
         ;; A ready standing await refines T5 followed by T6; a cold await is T5.
           :await (register! ctx action)
           :t06 (resume! ctx action)
           :t07 (complete! ctx action)
           :t08 (deliver! ctx action)
           :queued
           (let [event (first (:queue (header ctx w)))]
             (require! event ::empty-queue {:w w})
             (cond
               (:custody-dispatch event)
               (require! false ::unsupported-custody-dispatch {:w w :event event})
               (:completion event) (deliver! ctx (assoc event :w w :e (:completion event)))
               (:deferred-assignment event) (assign-deferred! ctx (assoc event :w w :e (:deferred-assignment event)))
               (:mailbox-post event) (process-mailbox-post! ctx (assoc event :w w :e (:mailbox-post event)))
               (:start-for event) (start-request! ctx w)
               (some event [:fdep-ended :cancelled :fork-released]) (cleanup! ctx w)
               (:register-host event)
               (let [e (:e event) o (:register-host event) er (read-row ctx w :entities e)]
                 (header-edit! ctx w update :queue #(vec (rest %)))
                 (if (and er (= :live (:status (header ctx w))))
                   (let [cached? (and (:completed? er)
                                      (not (#{:running :parked} (:status (read-row ctx w :runs (current-run ctx w e))))))]
                     (touch! ctx w e (:tok event))
                     (when cached?
                       (emit! ctx {:event :host-delivery :world w :o o})
                       (vswap! (:commands ctx) update (dec (count @(:commands ctx))) assoc :value (:result er)))
                     (when (or (not cached?) (and (:standing? (:ob event))
                                                  (or (not (:completed? er)) (reactive? ctx w (current-run ctx w e)))))
                       (add-obligation! ctx w o (:ob event))))
                   (emit! ctx {:event :host-delivery :world w :o o :value ::released})))
               :else (require! false ::unsupported-control {:w w :event event})))
           :t09 (reenter! ctx action)
           :t10 (supersede! ctx w (:r action))
           :t11 (cancel-run! ctx w (:r action) (:anchor action))
           :t13 (close-scope! ctx w (:scope action))
           :t34 (release-world! ctx action)
           :release-request (request-release! ctx action)
           :release-observe (observe-release! ctx action)
           :release-detach (detach-release! ctx action)
           :release-notify (notify-release! ctx action)
           :t14
           (let [pin? (:pin? action) e (:e action)]
             (when pin?
               (require! (= :live (:status (header ctx w))) ::not-live {:world w})
               (require! (read-row ctx w :entities e) ::missing-entity {:e e}))
             (header-edit! ctx w update :pins (if pin? conj disj) e)
             (mark! ctx w e))
           :t15
           (doseq [[r rr] (store/table-view tx w :runs)
                   :when (#{:running :parked} (:status rr))]
             (cancel-run! ctx w r nil))
           :t19 (fork-following! ctx action)
           :t36 (cleanup! ctx w)
           :t37 (start-request! ctx w)
           :t16 (handle-unreachable! ctx (:tok action))
           :t17 (gc-notify! ctx action)
           :t18 (release-idle! ctx action)
           :slice-enter
           (let [th (:th action) r (:r action)]
             (require! (not-any? (fn [o]
                                   (let [ob (read-row ctx w :obligations o) [_ dw e] (:debtor ob)]
                                     (mailbox-control ctx dw e)))
                                 (read-row ctx w :by-run-creditor r))
                       ::mailbox-claim-required {:w w :r r})
             (require! (= :running (:status (read-row ctx w :runs r))) ::not-running {:w w :r r})
             (require! (nil? (get-in (root-state ctx) [:env :threads th :run])) ::thread-busy {:th th})
             (require! (not-any? #(and (= w (:world %)) (= r (:run %)))
                                 (vals (get-in (root-state ctx) [:env :threads])))
                       ::slice-busy {:w w :r r})
             (when (get-in (root-state ctx) [:model :cps-exit?])
               (edit! ctx w :runs r assoc :cps-entered? true))
             (root-edit! ctx update-in [:env :threads th] merge
                         {:world w :scope r :run r :obligation-world w :executing? true}))
           :t38
           (let [th (:th action)
                 {:keys [world run] :as thread} (get-in (root-state ctx) [:env :threads th])]
             (require! run ::no-slice {:th th})
             (require! (not-any? #(and (= :timer-resource (:kind %)) (= [world run] (:owner %))
                                       (= th (:installer %)) (= :pending (:install %)))
                                 (vals (get-in (root-state ctx) [:env :native])))
                       ::timer-install-pending {:th th})
             (cleanup-exit! ctx thread)
             (root-edit! ctx update-in [:env :threads th]
                         #(-> % (assoc :run nil :scope nil :executing? false)
                              (dissoc :retired? :obligation-world :anchor :cleanup-ticket)))
             (when (and (= :unwinding (:status (read-row ctx world :runs run)))
                        (not (physical? ctx world run)))
               (remove-run! ctx world run)))
           :native-progress
           (let [row (get-in (root-state ctx) [:env :native (:n action)]) [world run] (:owner row)]
             (require! (not (or (protected-native? row) (#{:mailbox-callback :timer-resource} (:kind row))))
                       ::protected-cleanup {:n (:n action)})
             (root-edit! ctx update-in [:env :native (:n action)]
                         #(cond-> (merge % (select-keys action [:state :boundary?]))
                            (= :joined (:state action)) (dissoc :anchor)))
             (when (and (= :unwinding (:status (read-row ctx world :runs run)))
                        (not (physical? ctx world run)))
               (remove-run! ctx world run)))
           :thread-entry
           (do (require! (nil? (get-in (root-state ctx) [:env :threads (:th action) :run]))
                         ::thread-busy {:th (:th action)})
               (require! (and (nil? (get-in action [:thread :cleanup-ticket]))
                              (not (protected-native?
                                    (get-in (root-state ctx)
                                            [:env :native (cleanup-ticket (get-in action [:thread :world])
                                                                          (get-in action [:thread :run]))]))))
                         ::protected-cleanup {:th (:th action)})
               (root-edit! ctx assoc-in [:env :threads (:th action)] (:thread action)))
           :waiter-unregister (root-edit! ctx update-in [:env :waiters] dissoc (:token action))
           :t35
           (let [th (get action :th :foreign) op (:op action)]
             (require! (get-in (root-state ctx) [:env :threads th :world]) ::no-world {:thread th})
             (when (= :resume (:kind op)) (resume! ctx op)))
           :signal-write
           (let [e (:e action) er (read-row ctx w :entities e)]
             (when-let [op (:op action)]
               (let [participant (operation-row ctx op) ticket (get-in (root-state ctx) [:env :native (first op)])]
                 (require! (and participant (= :cps-finalization (:kind ticket))
                                (= w (first (:owner ticket))) (= (second op) (:sequence ticket))
                                (contains? (:frames participant) (:frame action))
                                (= (:parent participant) (current-run ctx w (first (:parent participant)))))
                           ::cleanup-only {:action action})))
             (require! (not= :released (:status (header ctx w))) ::released {:w w})
             (when-not (and unwinding? (nil? er))
               (require! (and (#{:signal :atom} (:kind er)) (or (:owner er) unwinding?)) ::released {:w w :e e}))
             (when er
               (edit! ctx w :entities e assoc :result (:value action))
               (when-not (false? (:publish? action))
                 (enqueue! ctx w {:completion e :debtor-world w :value (:value action) :source-change? true})
                 (doseq [v (set (for [[x v d] (:fdeps (header ctx w))
                                      :when (if (= :bundle x) (contains? d e) (= x e))] v))]
                   (enqueue! ctx v {:completion e :debtor-world w :value (:value action) :source-change? true})))))
           :unsubscribe
           (let [ob (read-row ctx w :obligations o)]
             (require! (or (nil? ob) (:standing? ob)) ::not-standing {:o o})
             (end-obligation! ctx w o :creditor-cancelled))
           (throw (ex-info "Unsupported kernel transition" {:action action})))
         (when (contains? action :fresh-runs)
           (require! (and (vector? (:fresh-runs action)) (empty? @(:fresh-runs ctx)))
                     ::unused-run-allocation {:remaining @(:fresh-runs ctx)}))
         (rule-l! ctx)
         (prune-ancestry! ctx)
         (refresh-timer-anchors! ctx)
         (refresh-releases! ctx)
         (when diagnostics? (root-edit! ctx assoc :events @(:events ctx)))
         {:events (if diagnostics? @(:events ctx) [])
          :commands @(:commands ctx) :result @(:result ctx)})))))
