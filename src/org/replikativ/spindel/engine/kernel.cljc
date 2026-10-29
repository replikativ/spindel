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
                           :scopes {[:root w] {:kind :world-root :parent nil :status :open}}
                           :entities {} :runs {} :obligations {} :releasing #{}
                           :fdeps #{} :pins #{} :queue []}}
               :registry #{w} :known-worlds #{w} :lineages {w lineage}
               :env {:handles {} :threads {:host {:world w :scope nil :run nil
                                                  :read-permits #{} :excl-permits []}}
                     :native {} :outside []}
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

(declare index-add! index-remove!)

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
  (some #(= o (:cancelled %)) (pending-events ctx w)))

(defn- pending-start? [ctx v o ob]
  (let [[kind w e] (:debtor ob)]
    (and (= :entity kind) (not= w v)
         (some #(or (and (= e (:start-for %)) (= v (:creditor-world %)) (= o (:o %)))
                    (and (= v (:join-bundle %)) (= e (get-in % [:members o :debtor]))))
               (pending-events ctx w)))))

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

(defn- end-obligation! [ctx w o cause]
  (when-let [ob (read-row ctx w :obligations o)]
    (let [[ck cw r] (:creditor ob)]
      (when (and (= :cancel-delivered cause) (= :await-reactive (:kind ob))
                 (= :consumed (:slot ob)) (= :run ck)
                 (#{:running :parked :inherited :completed} (:status (read-row ctx cw :runs r)))
                 (= r (current-run ctx cw (first r))))
        (edit! ctx cw :runs r assoc :validation-lost? true)
        (when (:completed? (read-row ctx cw :entities (first r)))
          (edit! ctx cw :entities (first r) assoc :dirty? true))))
    (delete! ctx w :obligations o)
    (index-remove! ctx w (creditor-table (:creditor ob)) (creditor-id (:creditor ob)) o)
    (index-remove! ctx w (debtor-table w (:debtor ob)) (debtor-id w (:debtor ob)) o)
    (when (and (= :entity (first (:debtor ob))) (not= w (second (:debtor ob))))
      (index-remove! ctx w :by-debtor-world (second (:debtor ob)) o))
    (if (:diagnostics? ctx)
      (emit! ctx {:event :obligation-exit :world w :o o :ob ob :cause cause})
      (command! ctx {:op :release-obligation :world w :o o :cause cause}))
    (when (and (= :cancel-delivered cause) (= :host (first (:creditor ob))))
      (emit! ctx {:event :host-delivery :world w :o o :value ::cancelled}))
    (let [[kind dw e] (:debtor ob)
          fd [e w o]]
      (when (and (= :entity kind) (not= w dw) (= :run (first (:creditor ob)))
                 (not= :released (:status (header ctx dw))))
        (when (contains? (:fdeps (header ctx dw)) fd)
          (cleanup-dependency! ctx dw fd))
        (sync-bundle! ctx dw w)))
    (when (and (= :external (:kind ob)) (:token ob))
      (root-edit! ctx assoc-in [:env :waiters (:token ob) :armed?] true))
    ob))

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
         (or (#{:signal :atom :keyed-entry :cache-row :fork} kind)
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

(declare cancel-run! supersede! close-scope! resume! rule-l!)

(defn- owner-chain [ctx w r]
  (loop [id r chain [] seen #{}]
    (cond
      (nil? id) (conj chain w)
      (seen id) chain
      (= :unwinding (:status (read-row ctx w :runs id)))
      (into chain (:anchor (read-row ctx w :runs id)))
      :else (recur (or (:owner (read-row ctx w :runs id))
                       (:parent (read-row ctx w :scopes id)))
                   (conj chain id) (conj seen id)))))

(defn- physical? [ctx w r]
  (let [env (:env (root-state ctx))]
    (or (some #(and (= w (:world %)) (= r (:run %))) (vals (:threads env)))
        (some #(and (= [w r] (:owner %)) (not= :joined (:state %))) (vals (:native env))))))

(defn- cleanup-ticket [w r] [:cps-exit w r])
(defn- cleanup-op? [row] (= :cps-exit (:kind row)))
(defn- protected-native? [row] (#{:cps-exit :cps-finalization} (:kind row)))

(defn- retain-cleanup! [ctx w scope]
  (when (get-in (root-state ctx) [:model :cps-exit?])
    (let [owners (loop [pending [scope] found #{}]
                   (if-let [id (peek pending)]
                     (if (found id) (recur (pop pending) found)
                         (recur (into (pop pending) (concat (read-row ctx w :runs-by-owner id)
                                                            (read-row ctx w :scopes-by-parent id)))
                                (conj found id))) found))]
      (doseq [r owners :let [row (read-row ctx w :runs r) n (cleanup-ticket w r)]
              :when (and (:cps-entered? row) (#{:running :parked :stale} (:status row))
                         (not (cleanup-op? (get-in (root-state ctx) [:env :native n]))))]
        (root-edit! ctx update-in [:env :native n]
                    #(assoc (or % {:owner [w r] :state :running :phase :ready
                                   :sequence (:finalization-sequence row 0)})
                            :kind :cps-exit :retired? true :anchor (owner-chain ctx w r))))
      (let [state (root-state ctx)
            participants (set (for [[n row] (get-in state [:env :native])
                                    :when (and (cleanup-op? row) (= w (first (:owner row)))
                                               (some owners (:anchor row)))] n))
            captured (into {} (for [owner owners e (read-row ctx w :entities-by-owner owner)
                                    :let [row (read-row ctx w :entities e)]
                                    :when (#{:signal :atom} (:kind row))]
                                [[w owner e] {:kind (:kind row) :result (:result row)}]))
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

(defn- finalization-resume! [ctx {:keys [n th] :as action}]
  (let [state (root-state ctx) row (get-in state [:env :native n]) [w r] (:owner row)
        rr (read-row ctx w :runs r) thread (get-in state [:env :threads th])
        inline? (and (:executing? thread) (= [w r] [(:world thread) (:run thread)]))]
    (require! (and (= :cps-finalization (:kind row)) (= :ready (:phase row))) ::not-ready {:n n})
    (require! (= w (:w action)) ::wrong-world {:n n :w (:w action)})
    (require! (and (= :parked (:status rr)) (= r (current-run ctx w (:spin rr))))
              ::not-current-slice {:n n})
    (require! (or inline? (nil? (:run thread))) ::thread-busy {:th th})
    (require! (or inline? (not-any? #(and (= w (:world %)) (= r (:run %)))
                                    (vals (:threads (:env state))))) ::slice-busy {:w w :r r})
    (root-edit! ctx update-in [:env :native] dissoc n)
    (edit! ctx w :runs r assoc :status :running)
    (when-not inline?
      (root-edit! ctx assoc-in [:env :threads th]
                  (merge thread {:world w :scope r :run r :obligation-world w :executing? true})))))

(defn- cleanup-claim! [ctx {:keys [n th]}]
  (let [state (root-state ctx) row (get-in state [:env :native n]) [w r] (:owner row)]
    (require! (and (cleanup-op? row) (= :ready (:phase row))) ::not-ready {:n n})
    (require! (nil? (get-in state [:env :threads th :run])) ::thread-busy {:th th})
    (require! (not-any? #(and (= w (:world %)) (= r (:run %)))
                        (vals (get-in state [:env :threads]))) ::slice-busy {:w w :r r})
    (root-edit! ctx assoc-in [:env :native n :phase] :claimed)
    (root-edit! ctx update-in [:env :threads th] merge
                {:world w :scope r :run r :executing? true :retired? true
                 :obligation-world w :anchor (:anchor row) :cleanup-ticket n})))

(defn- cleanup-adopt! [ctx {:keys [n th]}]
  (let [state (root-state ctx) row (get-in state [:env :native n])
        thread (get-in state [:env :threads th])]
    (require! (and (cleanup-op? row) (= :ready (:phase row))) ::not-ready {:n n})
    (require! (and (:executing? thread) (= (:owner row) [(:world thread) (:run thread)])
                   (nil? (:cleanup-ticket thread))) ::wrong-slice {:n n :th th})
    (root-edit! ctx assoc-in [:env :native n :phase] :claimed)
    (root-edit! ctx update-in [:env :threads th] assoc :cleanup-ticket n
                :retired? true :anchor (:anchor row))))

(defn- cleanup-boundary! [ctx {:keys [th]} phase]
  (let [n (get-in (root-state ctx) [:env :threads th :cleanup-ticket])
        row (get-in (root-state ctx) [:env :native n])]
    (require! (and n (= :claimed (:phase row))) ::not-claimed {:th th})
    (root-edit! ctx update-in [:env :native n]
                #(cond-> (-> % (assoc :phase phase) (dissoc :delivery))
                   (= :waiting phase) (update :sequence inc)))))

(defn- cleanup-deliver! [ctx {:keys [n sequence value]}]
  (let [row (get-in (root-state ctx) [:env :native n])]
    (when (and (protected-native? row) (= :waiting (:phase row)) (= sequence (:sequence row)))
      (root-edit! ctx update-in [:env :native n] assoc :phase :ready :delivery value))))

(defn- cleanup-access! [ctx {:keys [th cell value] :as action}]
  (let [n (get-in (root-state ctx) [:env :threads th :cleanup-ticket])
        row (get-in (root-state ctx) [:env :native n])]
    (require! (and n (= :claimed (:phase row)) (contains? (:cells row) cell))
              ::missing-cleanup-cell {:th th :cell cell})
    (when (contains? action :value)
      (root-edit! ctx assoc-in [:env :cleanup-cells cell :result] value))))

(defn- cleanup-exit! [ctx thread]
  (when-let [n (:cleanup-ticket thread)]
    (let [row (get-in (root-state ctx) [:env :native n])]
      (require! (#{:ready :waiting :returning} (:phase row)) ::missing-cleanup-boundary
                {:n n :phase (:phase row)})
      (when (= :returning (:phase row))
        (doseq [key (:cells row)]
          (let [holders (disj (get-in (root-state ctx) [:env :cleanup-cells key :holders]) n)]
            (if (seq holders)
              (root-edit! ctx assoc-in [:env :cleanup-cells key :holders] holders)
              (root-edit! ctx update-in [:env :cleanup-cells] dissoc key))))
        (root-edit! ctx update-in [:env :native] dissoc n)))))

(defn- remove-run! [ctx w r]
  (when-let [rr (read-row ctx w :runs r)]
    (index-remove! ctx w :runs-by-spin (:spin rr) r)
    (index-remove! ctx w :runs-by-owner (:owner rr) r)
    (doseq [parent (read-row ctx w :spawned-by r)]
      (when (read-row ctx w :runs parent)
        (edit! ctx w :runs parent update :spawned disj r)))
    (delete! ctx w :runs r)))

(defn- release-entity! [ctx w e]
  (when-let [er (read-row ctx w :entities e)]
    (if (= :spin (:kind er))
      (edit-entity! ctx w e assoc :owner nil :dirty? true)
      (edit-entity! ctx w e assoc :owner nil))
    (doseq [r (read-row ctx w :runs-by-spin e)]
      (case (:status (read-row ctx w :runs r))
        (:running :parked) (cancel-run! ctx w r nil)
        (:completed :stale) (supersede! ctx w r)
        nil))
    (doseq [o (entity-obligations ctx w w e)]
      (let [ob (read-row ctx w :obligations o)]
        (when (= :run (first (:creditor ob)))
          (resume! ctx {:w w :o o :value ::cancelled}))
        (end-obligation! ctx w o :cancel-delivered)))))

(defn- release-owned! [ctx w scope]
  (doseq [e (read-row ctx w :entities-by-owner scope)]
    (release-entity! ctx w e)))

(defn- retire-run! [ctx w r cause effects anchor]
  (retain-cleanup! ctx w r)
  (let [rr (if (physical? ctx w r) (cells/value (read-row ctx w :runs r)) (read-row ctx w :runs r))
        chain (or anchor (owner-chain ctx w r))
        scopes (loop [parents [r] found #{}]
                 (if-let [parent (first parents)]
                   (let [children (read-row ctx w :scopes-by-parent parent)]
                     (recur (into (vec (rest parents)) children) (into found children)))
                   found))]
    (doseq [s (read-row ctx w :scopes-by-parent r)]
      (close-scope! ctx w s))
    (doseq [s scopes]
      (let [row (read-row ctx w :scopes s)]
        (index-remove! ctx w :scopes-by-parent (:parent row) s)
        (delete! ctx w :scopes s)))
    (doseq [o (read-row ctx w :by-run-creditor r)]
      (end-obligation! ctx w o :creditor-cancelled))
    (root-edit! ctx update-in [:env :native]
                (fn [ops]
                  (into {} (map (fn [[n row]]
                                  [n (if (and (= [w r] (:owner row)) (not= :joined (:state row))
                                              (not (protected-native? row)))
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
        (edit! ctx w :entities e assoc :creator nil)))))

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

(defn- cancel-foreign-debtor! [ctx w v o]
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
    (enqueue! ctx v {:cancelled o})
    (when-not (some (fn [other]
                      (let [ob (read-row ctx v :obligations other)]
                        (and (not= o other) (= :run (first (:creditor ob)))
                             (= :inherited (:status (read-row ctx v :runs (nth (:creditor ob) 2))))
                             (not (pending-start? ctx v other ob)) (not (cancelling? ctx v other)))))
                    (entity-obligations ctx v w e))
      (header-edit! ctx w update :fdeps
                    #(set (keep (fn [[tag target debtors :as fd]]
                                  (if (and (= :bundle tag) (= v target))
                                    (when (seq (disj debtors e)) [:bundle v (disj debtors e)]) fd)) %))))))

(defn- supersede! [ctx w r]
  (when-let [rr (read-row ctx w :runs r)]
    (require! (#{:completed :stale} (:status rr)) ::not-predecessor {:r r})
    (let [chain (owner-chain ctx w r)]
      (retire-run!
       ctx w r :superseded
       (fn []
         (doseq [child (read-row ctx w :runs-by-owner r)]
           (cancel-run! ctx w child (into [child] chain)))
         (doseq [e (read-row ctx w :entities-by-owner r)
                 :when (#{:cache-row :keyed-entry} (:kind (read-row ctx w :entities e)))]
           (index-remove! ctx w :entities-by-owner r e)
           (delete! ctx w :entities e))
         (release-owned! ctx w r))
       chain))))

(defn- cancel-run! [ctx w r anchor]
  (when-let [rr (read-row ctx w :runs r)]
    (when-not (= :unwinding (:status rr))
      (let [e (:spin rr)
            current? (= r (current-run ctx w e))
            chain (or anchor (owner-chain ctx w r))]
        (retire-run!
         ctx w r :cancelled
         (fn []
           (doseq [child (read-row ctx w :runs-by-owner r)]
             (cancel-run! ctx w child (into [child] chain)))
           (when current?
             (doseq [o (entity-obligations ctx w w e)]
               (let [ob (read-row ctx w :obligations o)]
                 (when (= :run (first (:creditor ob)))
                   (resume! ctx {:w w :o o :value ::cancelled}))
                 (end-obligation! ctx w o :cancel-delivered)))
             (doseq [[v o] (foreign-creditors ctx w e)]
               (cancel-foreign-debtor! ctx w v o))
             (when (= :stale (:status (read-row ctx w :runs (:pred rr))))
               (supersede! ctx w (:pred rr))))
           (release-owned! ctx w r)
           (when (read-row ctx w :entities e)
             (edit! ctx w :entities e assoc :dirty? true)))
         chain)))))

(defn- close-scope! [ctx w scope]
  (require! (not= scope (:root (header ctx w))) ::world-release-not-implemented {:w w})
  (when (and (not= :released (:status (header ctx w))) (open? ctx w scope))
    (retain-cleanup! ctx w scope)
    (doseq [s (read-row ctx w :scopes-by-parent scope)]
      (close-scope! ctx w s))
    (doseq [r (read-row ctx w :runs-by-owner scope)]
      (cancel-run! ctx w r nil))
    (release-owned! ctx w scope)
    (edit! ctx w :scopes scope assoc :status :closed)))

(defn- remove-entity! [ctx w e]
  (when-let [er (read-row ctx w :entities e)]
    (doseq [r (read-row ctx w :runs-by-spin e)]
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
          (or (#{:signal :atom} (:kind er)) (:dirty? er)) true
          :else
          (recur (into todo (for [r (read-row ctx w :runs-by-spin e)
                                  o (read-row ctx w :by-run-creditor r)
                                  :let [ob (read-row ctx w :obligations o)
                                        [dk dw de] (:debtor ob)]
                                  :when (and (#{:track :await-reactive} (:kind ob)) (= :entity dk))]
                              [dw de]))
                 (conj seen key))))
      false)))

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
                                         (not (execution-live? ctx w e)))] e))]
          (doseq [e idle
                  :let [er (read-row ctx w :entities e)
                        runs (vec (read-row ctx w :runs-by-spin e))]]
            (when (or (:owner er)
                      (some #(#{:completed :stale} (:status (read-row ctx w :runs %))) runs))
              (vreset! changed? true))
            (when (signal-dependent? ctx w e)
              (when-not (:dirty? er) (vreset! changed? true))
              (edit-entity! ctx w e assoc :dirty? true))
            (doseq [r runs :when (#{:completed :stale} (:status (read-row ctx w :runs r)))]
              (supersede! ctx w r))
            (when (read-row ctx w :entities e)
              (edit-entity! ctx w e assoc :owner nil)))
          (let [dead (vec (for [[e er] (store/table-view (:tx ctx) w :entities)
                                :when (and (not (wanted? ctx w e))
                                           (not (and (= :spin (:kind er)) (:completed? er) (seq (:tokens er)))))] e))]
            (doseq [e dead] (vreset! changed? true) (remove-entity! ctx w e)))
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
      (do (put-entity! ctx w e (assoc (entity-row kind scope) :key key :result value :order order))
          (when (read-row ctx w :runs scope)
            (edit! ctx w :runs scope update :creations conj e))))))

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
  (require! (= :live (:status (header ctx w))) ::sealed {:world w})
  (require! (open? ctx w scope) ::closed-scope {:world w :scope scope})
  (doseq [r (read-row ctx w :runs-by-spin e)
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
      (doseq [r (read-row ctx w :runs-by-spin e)
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
      (doseq [r (read-row ctx w :runs-by-spin e)
              :when (= previous-creator (:owner (read-row ctx w :runs r)))]
        (move-run-owner! ctx w r scope)))
    (touch! ctx w e tok)))

(defn- reenter! [ctx {:keys [w e cause order resume-o] :or {cause :dirty order -1}}]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (let [r (current-run ctx w e)
        rr (read-row ctx w :runs r)]
    (require! rr ::missing-run {:e e})
    (doseq [p (read-row ctx w :runs-by-spin e)
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
        (if (and work? (= :track (:kind ob)) (<= (:order ob) order))
          (do (index-remove! ctx w :by-run-creditor r o)
              (edit! ctx w :obligations o assoc :creditor [:run w r2])
              (index-add! ctx w :by-run-creditor r2 o))
          (when work? (end-obligation! ctx w o :creditor-cancelled))))
      (doseq [scope (read-row ctx w :scopes-by-parent r)
              :when (< (get (read-row ctx w :scopes scope) :order 0) order)]
        (index-remove! ctx w :scopes-by-parent r scope)
        (edit! ctx w :scopes scope assoc :parent r2)
        (index-add! ctx w :scopes-by-parent r2 scope))
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
        _ (when (and (= dk :entity) (= dw w)
                     (#{:await-once :await-reactive} kind)
                     (nil? (read-row ctx w :entities e)))
            (put-entity! ctx w e (spin-row ctx w e r)))
        _ (when (and (= dk :entity) (= dw w) (#{:await-once :await-reactive} kind))
            (adopt-call-target! ctx w e r))
        er (when (= dk :entity) (read-row ctx dw :entities e))
        await? (and (= dk :entity) (#{:await-once :await-reactive} kind))
        _ (when (and await? (= w dw) (nil? (:owner er)))
            (edit-entity! ctx dw e assoc :owner r))
        work? (some #(#{:running :parked} (:status (read-row ctx dw :runs %)))
                    (read-row ctx dw :runs-by-spin e))
        completed? (and (:completed? er)
                        (or (not= w dw) (and (not (:dirty? er)) (not work?))))
        foreign-cold? (and await? (not= w dw) (not work?) (not (:completed? er)))]
    (require! (or (not= dk :entity) er foreign-cold?) ::missing-debtor {:debtor debtor})
    (when (and await? (= w dw) (not work?) (not completed?))
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

(defn- resume! [ctx {:keys [w o value direct?] :or {value :value}}]
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
        (doseq [id (read-row ctx w :by-run-creditor r)
                :let [other (read-row ctx w :obligations id)
                      [_ dw _] (:debtor other)
                      token [:cancel w id]]]
          (add-fdep! ctx w id)
          (when (and dw (not= dw w)) (sync-bundle! ctx dw w))
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
          (command! ctx {:op :resume :world w :run r :o o :cont (:cont ob) :value value}))))))

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
      (doseq [pred (read-row ctx w :runs-by-spin e) :when (not= r pred)]
        (when (#{:completed :stale} (:status (read-row ctx w :runs pred)))
          (supersede! ctx w pred)))
      (doseq [child (read-row ctx w :entities-by-owner r)
              :let [row (read-row ctx w :entities child)]
              :when (#{:timer :waiter} (:kind row))]
        (index-remove! ctx w :entities-by-owner r child)
        (delete! ctx w :entities child)))))

(defn- deliver! [ctx {:keys [w e debtor-world value]}]
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

(defn- fork-following! [ctx {:keys [w v k scope systems] :or {systems #{:a :b}}}]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (require! (open? ctx w scope) ::closed-scope {:scope scope})
  (require! (not (contains? (:known-worlds (root-state ctx)) v)) ::world-id-reused {:world v})
  (let [copy-row #(assoc (cells/value %) :origin :inherited :source-world w)
        runs (into {} (for [[r rr] (store/table-view (:tx ctx) w :runs)
                            :when (= :parked (:status rr))]
                        [r (assoc (copy-row rr) :status :inherited :owner [:root v])]))
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
               :entities entities :runs runs :obligations obligations
               :releasing #{} :fdeps #{} :pins #{} :queue queue :seq (get (header ctx w) :seq 0)}
        last-seq (reduce max (:seq child) (keep :seq queue))
        durable? (boolean (seq (set/intersection systems (get-in (root-state ctx) [:model :durable-systems]))))
        cap {:world v :scope systems :holder scope :disposition :open :published? true
             :op nil :pred nil :successors [] :durable? durable?
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
    (root-edit! ctx update :caps dissoc k)
    (root-edit! ctx update-in [:durable :caps] dissoc k)
    (root-edit! ctx assoc-in (if durable? [:durable :caps k] [:caps k]) cap)
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
    (header-edit! ctx w update :queue #(vec (rest %)))
    (when pending?
      (if (not= :live (:status (header ctx w)))
        (enqueue! ctx v {:cancelled o :value ::released})
        (let [owner (:root (header ctx w))]
          (when-not (read-row ctx w :entities e) (put-entity! ctx w e (spin-row ctx w e owner)))
          (let [er (read-row ctx w :entities e)
                completed? (:completed? er)
                value (:result er)]
            (when-not (or completed? (#{:running :parked} (:status (read-row ctx w :runs (current-run ctx w e)))))
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
        (:cancelled event) (do (resume! ctx {:w w :o (:cancelled event) :value (get event :value ::cancelled)})
                               (end-obligation! ctx w (:cancelled event) :cancel-delivered))
        (:fork-released event) (remove-entity! ctx w [:fork (:fork-released event)])
        :else (require! false ::not-cleanup {:event event})))))

(defn step!
  "Execute a supported transition, returning delivery descriptors after commit.
  Unsupported actions refuse explicitly; this is not yet the runtime engine."
  [kernel {:keys [t w o] :as action}]
  (store/transact!
   kernel
   (fn [tx]
     (let [diagnostics? (get (store/options kernel) :diagnostics? true)
           ctx {:tx tx :events (when diagnostics? (volatile! [])) :work (volatile! [])
                :work-set (volatile! #{}) :commands (volatile! []) :result (volatile! nil)
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
       (when (contains? action :fresh-runs)
         (require! (and (vector? (:fresh-runs action))
                        (every? #(and (vector? %) (= 3 (count %))) (:fresh-runs action)))
                   ::invalid-run-allocation {:action action}))
       (when (and slice? (not (#{:t38 :cleanup-adopt :cleanup-park :cleanup-return :cleanup-cell} t)) (= :released (:status (header ctx (:world thread)))))
         (require! false ::released {:w w :thread (:th action)}))
       (when (and unwinding? (#{:t01 :t02 :t03 :t04 :t05 :t12 :t19 :t20 :t20q} t))
         (require! false ::cancelled {:w w :r (:run thread)}))
       (when (and (or (:cleanup-ticket thread)
                      (cleanup-op? (get-in (root-state ctx) [:env :native (cleanup-ticket (:world thread) (:run thread))])))
                  (not (#{:t38 :cleanup-adopt :cleanup-park :cleanup-return :cleanup-cell} t)))
         (require! false ::cleanup-only {:thread (:th action) :action action}))
       (case t
         :finalization-wait (finalization-wait! ctx action)
         :finalization-resume (finalization-resume! ctx action)
         :cleanup-adopt (cleanup-adopt! ctx action)
         :cleanup-claim (cleanup-claim! ctx action)
         :cleanup-park (cleanup-boundary! ctx action :waiting)
         :cleanup-return (cleanup-boundary! ctx action :returning)
         :cleanup-deliver (cleanup-deliver! ctx action)
         :cleanup-cell (cleanup-access! ctx action)
         :t01 (create-spin! ctx action)
         :t02
         (create-source! ctx action)
         :t04 (invoke! ctx action)
         :t03
         (let [r (:r action)
               rr (read-row ctx w :runs r)]
           (require! (#{:running :parked} (:status rr)) ::not-work {:r r})
           (let [e [(:spin rr) (:key action)]]
             (put-entity! ctx w e
                          (assoc (entity-row (get action :kind :cache-row) r)
                                 :order (get action :order 0)))
             (edit! ctx w :runs r update :creations conj e)))
         :t12
         (do (require! (= :live (:status (header ctx w))) ::not-live {:world w})
             (require! (open? ctx w (:parent action)) ::closed-scope {:parent (:parent action)})
             (put! ctx w :scopes (:scope action)
                   (cond-> {:kind (get action :kind :explicit) :parent (:parent action) :status :open}
                     (read-row ctx w :runs (:parent action)) (assoc :order (get action :order 0))))
             (index-add! ctx w :scopes-by-parent (:parent action) (:scope action)))
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
             (:completion event) (deliver! ctx (assoc event :w w :e (:completion event)))
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
           (cleanup-exit! ctx thread)
           (root-edit! ctx update-in [:env :threads th]
                       #(-> % (assoc :run nil :scope nil :executing? false)
                            (dissoc :retired? :obligation-world :anchor :cleanup-ticket)))
           (when (and (= :unwinding (:status (read-row ctx world :runs run)))
                      (not (physical? ctx world run)))
             (remove-run! ctx world run)))
         :native-progress
         (let [row (get-in (root-state ctx) [:env :native (:n action)]) [world run] (:owner row)]
           (require! (not (protected-native? row)) ::protected-cleanup {:n (:n action)})
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
           (require! (not= :released (:status (header ctx w))) ::released {:w w})
           (when-not (and unwinding? (nil? er))
             (require! (and (#{:signal :atom} (:kind er)) (or (:owner er) unwinding?)) ::released {:w w :e e}))
           (when er
             (edit! ctx w :entities e assoc :result (:value action))
             (enqueue! ctx w {:completion e :debtor-world w :value (:value action) :source-change? true})
             (doseq [v (set (for [[x v d] (:fdeps (header ctx w))
                                  :when (if (= :bundle x) (contains? d e) (= x e))] v))]
               (enqueue! ctx v {:completion e :debtor-world w :value (:value action) :source-change? true}))))
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
       (when diagnostics? (root-edit! ctx assoc :events @(:events ctx)))
       {:events (if diagnostics? @(:events ctx) [])
        :commands @(:commands ctx) :result @(:result ctx)}))))
