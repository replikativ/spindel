(ns org.replikativ.spindel.engine.kernel
  "Transition kernel under construction. Owns canonical lifetime rows and
  indexes in an owned store; never invokes user continuations under its gate."
  (:require [org.replikativ.spindel.engine.owned-store :as store]))

(def ^:private environment ::environment)
(def ^:private world-tables #{:entities :runs :obligations :scopes})

(defn- index-add [index k id] (update index k (fnil conj #{}) id))

(defn- encode-world [world]
  (let [obs (:obligations world)]
    (merge (select-keys world world-tables)
           {:header {:world (apply dissoc world world-tables)}
            :by-creditor (reduce-kv #(index-add %1 (:creditor %3) %2) {} obs)
            :by-debtor (reduce-kv #(index-add %1 (:debtor %3) %2) {} obs)
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
  [state]
  (store/create-store
   (assoc (reduce-kv #(assoc %1 %2 (encode-world %3)) {} (:worlds state))
          environment {:state {:root (dissoc state :worlds)}})))

(defn snapshot [kernel]
  (let [view (store/snapshot kernel)]
    (assoc (get-in view [environment :state :root]) :worlds
           (reduce-kv (fn [worlds w tables]
                        (if (= environment w) worlds
                            (assoc worlds w
                                   (merge (get-in tables [:header :world])
                                          (select-keys tables world-tables)))))
                      {} view))))

(defn create-kernel []
  (let [w [:w 0]]
    (restore {:worlds {w {:id w :lineage {:parent nil :root w :mode :root :cut nil :basis nil}
                          :status :live :admission :open :seal-seq nil :root [:root w]
                          :scopes {[:root w] {:kind :world-root :parent nil :status :open}}
                          :entities {} :runs {} :obligations {} :releasing #{}
                          :fdeps #{} :pins #{} :queue []}}
              :env {:handles {} :threads {:host {:world w :scope nil :run nil
                                                 :read-permits #{} :excl-permits []}}
                    :native {} :outside []}
              :serial {} :events []})))

(defn- read-row [ctx w table id]
  (store/read-row (:tx ctx) w table id))

(defn- mark! [ctx w e]
  (when (and e (:work ctx)) (vswap! (:work ctx) conj [w e])))

(defn- mark-owner! [ctx w scope]
  (loop [scope scope seen #{}]
    (when-let [run (when-not (seen scope) (read-row ctx w :runs scope))]
      (mark! ctx w (:spin run))
      (recur (:owner run) (conj seen scope)))))

(defn- mark-row! [ctx w table id old value]
  (case table
    :entities (do (mark! ctx w id)
                  (mark-owner! ctx w (:owner old))
                  (mark-owner! ctx w (:owner value)))
    :runs (do (mark! ctx w (:spin old))
              (mark! ctx w (:spin value))
              (mark-owner! ctx w (:owner old))
              (mark-owner! ctx w (:owner value)))
    :obligations (doseq [ob [old value]
                         :let [[kind dw e] (:debtor ob)]
                         :when (= :entity kind)]
                   (mark! ctx dw e))
    nil))

(declare index-add! index-remove!)

(defn- index-run-links! [ctx w r old value]
  (doseq [[field index] [[:spawned :spawned-by] [:creations :created-by]]
          :let [before (get old field #{}) after (get value field #{})]]
    (doseq [id before :when (not (contains? after id))]
      (index-remove! ctx w index id r))
    (doseq [id after :when (not (contains? before id))]
      (index-add! ctx w index id r))))

(defn- put! [ctx w table id value]
  (let [old (read-row ctx w table id)]
    (when-not (= old value)
      (store/put-row! (:tx ctx) w table id value)
      (when (= :runs table) (index-run-links! ctx w id old value))
      (mark-row! ctx w table id old value)))
  value)

(defn- delete! [ctx w table id]
  (when-let [old (read-row ctx w table id)]
    (store/delete-row! (:tx ctx) w table id)
    (when (= :runs table) (index-run-links! ctx w id old nil))
    (mark-row! ctx w table id old nil)))

(defn- edit! [ctx w table id f & args]
  (put! ctx w table id (apply f (read-row ctx w table id) args)))

(defn- root-state [ctx] (read-row ctx environment :state :root))
(defn- root-edit! [ctx f & args]
  (apply edit! ctx environment :state :root f args))
(defn- header [ctx w] (read-row ctx w :header :world))
(defn- header-edit! [ctx w f & args]
  (apply edit! ctx w :header :world f args))

(defn- require! [test error data]
  (when-not test (throw (ex-info (name error) (assoc data :error error)))))

(defn- emit! [ctx event] (vswap! (:events ctx) conj event))

(defn- enqueue! [ctx w event]
  (require! (not= :fenced (:admission (header ctx w)))
            ::fenced-enqueue-not-implemented {:w w})
  (let [n (inc (max (get (header ctx w) :seq 0)
                    (get-in (root-state ctx) [:clocks w] 0)))]
    (root-edit! ctx assoc-in [:clocks w] n)
    (header-edit! ctx w update :queue conj (assoc event :seq n))))

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
  (index-add! ctx w :by-creditor (:creditor ob) o)
  (index-add! ctx w :by-debtor (:debtor ob) o))

(defn- end-obligation! [ctx w o cause]
  (when-let [ob (read-row ctx w :obligations o)]
    (delete! ctx w :obligations o)
    (index-remove! ctx w :by-creditor (:creditor ob) o)
    (index-remove! ctx w :by-debtor (:debtor ob) o)
    (emit! ctx {:event :obligation-exit :world w :o o :ob ob :cause cause})
    (when (and (= :cancel-delivered cause) (= :host (first (:creditor ob))))
      (emit! ctx {:event :host-delivery :world w :o o :value ::cancelled}))
    (let [[kind dw e] (:debtor ob)
          fd [e w o]]
      (when (and (= :entity kind) (not= w dw)
                 (= :run (first (:creditor ob)))
                 (contains? (:fdeps (header ctx dw)) fd))
        (header-edit! ctx dw update :fdeps disj fd)
        (header-edit! ctx dw update :releasing conj fd)
        (enqueue! ctx dw {:fdep-ended fd})))
    (when (and (= :external (:kind ob)) (:token ob))
      (root-edit! ctx assoc-in [:env :waiters (:token ob) :armed?] true))
    ob))

(defn- touch! [ctx w e tok]
  (when (and tok (read-row ctx w :entities e))
    (edit! ctx w :entities e update :tokens (fnil conj #{}) tok)
    (root-edit! ctx update-in [:env :handles tok :touched] (fnil conj #{}) w)))

(defn- current-run [ctx w e]
  (last (sort-by second (read-row ctx w :runs-by-spin e))))

(defn- open? [ctx w scope]
  (if-let [run (read-row ctx w :runs scope)]
    (not= :unwinding (:status run))
    (= :open (:status (read-row ctx w :scopes scope)))))

(defn- entity-row [kind owner]
  {:kind kind :origin :created :owner owner :creator nil :completed? false
   :kept? false :result nil :tokens #{} :key nil :order 0})

(defn- put-entity! [ctx w e row]
  (when-let [old (read-row ctx w :entities e)]
    (index-remove! ctx w :entities-by-owner (:owner old) e))
  (put! ctx w :entities e row)
  (index-add! ctx w :entities-by-owner (:owner row) e))

(defn- spin-row [ctx w e owner]
  (assoc (entity-row :spin owner) :tokens
         (set (for [[tok h] (get-in (root-state ctx) [:env :handles])
                    :when (and (= e (:spin h)) (:reachable? h)
                               (contains? (:touched h) w)
                               (not (contains? (:dropped h) w)))] tok))))

(defn- reasons [ctx w e]
  (let [{:keys [kind owner completed? kept?]} (read-row ctx w :entities e)
        h (header ctx w)
        runs (map #(read-row ctx w :runs %) (read-row ctx w :runs-by-spin e))]
    (cond-> #{}
      (and owner (open? ctx w owner)
           (or (#{:signal :atom :keyed-entry :cache-row :fork} kind)
               (and (#{:timer :waiter} kind)
                    (#{:running :parked :inherited} (:status (read-row ctx w :runs owner))))
               (and (= :spin kind) (or (not completed?) kept?)))) (conj :own)
      (some #(#{:running :parked :inherited :stale} (:status %)) runs) (conj :active)
      (or (seq (read-row ctx w :by-debtor [:entity w e]))
          (seq (read-row ctx w :by-creditor [:entity w e]))) (conj :obl)
      (some (fn [[x _ d]] (if (= :bundle x) (contains? d e) (= x e)))
            (concat (:fdeps h) (:releasing h))) (conj :dep)
      (some (fn [r]
              (and (= :completed (:status (read-row ctx w :runs r)))
                   (or (some #(not= :unwinding (:status (read-row ctx w :runs %)))
                             (read-row ctx w :runs-by-owner r))
                       (some #(and (not= % e) (seq (reasons ctx w %)))
                             (read-row ctx w :entities-by-owner r)))))
            (read-row ctx w :runs-by-spin e)) (conj :scope)
      (contains? (:pins h) e) (conj :pin))))

(defn- owner [ctx w action]
  (let [thread (get-in (root-state ctx) [:env :threads (get action :th :host)])]
    (or (:scope action) (:scope thread) (:r action) (:run thread) (:root (header ctx w)))))

(defn- reactive? [ctx w r]
  (boolean
   (some (fn [o]
           (let [ob (read-row ctx w :obligations o)]
             (and (:standing? ob) (#{:track :await-reactive} (:kind ob)))))
         (read-row ctx w :by-creditor [:run w r]))))

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
    (put-entity! ctx w e (cond-> (assoc er :owner nil)
                           (= :spin (:kind er)) (assoc :dirty? true)))
    (doseq [r (read-row ctx w :runs-by-spin e)]
      (case (:status (read-row ctx w :runs r))
        (:running :parked) (cancel-run! ctx w r nil)
        (:completed :stale) (supersede! ctx w r)
        nil))
    (doseq [o (read-row ctx w :by-debtor [:entity w e])]
      (let [ob (read-row ctx w :obligations o)]
        (when (= :run (first (:creditor ob)))
          (resume! ctx {:w w :o o :value ::cancelled}))
        (end-obligation! ctx w o :cancel-delivered)))))

(defn- release-owned! [ctx w scope]
  (doseq [e (read-row ctx w :entities-by-owner scope)]
    (release-entity! ctx w e)))

(defn- retire-run! [ctx w r cause effects anchor]
  (let [rr (read-row ctx w :runs r)
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
    (doseq [o (read-row ctx w :by-creditor [:run w r])]
      (end-obligation! ctx w o :creditor-cancelled))
    (root-edit! ctx update-in [:env :native]
                (fn [ops]
                  (into {} (map (fn [[n row]]
                                  [n (if (and (= [w r] (:owner row)) (not= :joined (:state row)))
                                       (assoc row :state :cancel-requested) row)])) ops)))
    (emit! ctx {:event :run-exit :world w :r r :cause cause
                :t (if (= cause :superseded) :t10 :t11)})
    (effects)
    (remove-run! ctx w r)
    (when (physical? ctx w r)
      (put! ctx w :runs r
            (assoc rr :status :unwinding :owner nil :anchor chain :retired? true
                   :creations #{} :spawned #{} :pred nil))
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
             (doseq [o (read-row ctx w :by-debtor [:entity w e])]
               (let [ob (read-row ctx w :obligations o)]
                 (when (= :run (first (:creditor ob)))
                   (resume! ctx {:w w :o o :value ::cancelled}))
                 (end-obligation! ctx w o :cancel-delivered)))
             (doseq [[x v o :as fd] (:fdeps (header ctx w)) :when (= x e)]
               (header-edit! ctx w update :fdeps disj fd)
               (enqueue! ctx v {:cancelled o :value ::cancelled}))
             (when (= :stale (:status (read-row ctx w :runs (:pred rr))))
               (supersede! ctx w (:pred rr))))
           (release-owned! ctx w r)
           (when (read-row ctx w :entities e)
             (edit! ctx w :entities e assoc :dirty? true)))
         chain)))))

(defn- close-scope! [ctx w scope]
  (require! (not= scope (:root (header ctx w))) ::world-release-not-implemented {:w w})
  (when (and (not= :released (:status (header ctx w))) (open? ctx w scope))
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
    (header-edit! ctx w update :pins disj e)
    (header-edit! ctx w update :queue
                  #(vec (remove (fn [event]
                                  (or (and (= e (:completion event)) (= w (:debtor-world event)))
                                      (= e (:signal-write event)))) %)))
    (doseq [creator (read-row ctx w :created-by e)]
      (when (read-row ctx w :runs creator)
        (edit! ctx w :runs creator update :creations disj e)))))

(defn- rule-l! [ctx]
  (loop [cursor 0]
    (when (< cursor (count @(:work ctx)))
      (let [[w e] (nth @(:work ctx) cursor)
            er (read-row ctx w :entities e)]
        (when (and er (not= :released (:status (header ctx w))) (empty? (reasons ctx w e)))
          (when (and (= :spin (:kind er)) (:completed? er))
            (doseq [r (read-row ctx w :runs-by-spin e)]
              (when (#{:completed :stale} (:status (read-row ctx w :runs r)))
                (supersede! ctx w r)))
            (when-let [row (read-row ctx w :entities e)]
              (put-entity! ctx w e (assoc row :owner nil))))
          (when-let [row (read-row ctx w :entities e)]
            (when (and (empty? (reasons ctx w e))
                       (not (and (= :spin (:kind row)) (:completed? row) (seq (:tokens row)))))
              (remove-entity! ctx w e))))
        (recur (inc cursor))))))

(defn- predecessor? [ctx w previous r]
  (loop [p (:pred (read-row ctx w :runs r))]
    (cond (nil? p) false
          (= p previous) true
          :else (recur (:pred (read-row ctx w :runs p))))))

(defn- create-source! [ctx {:keys [w e key value kind] :or {kind :signal} :as action}]
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
          (put-entity! ctx w e (assoc er :owner scope))))
      (put-entity! ctx w e (assoc (entity-row kind scope) :key key :result value)))))

(defn- start-run! [ctx w e scope cause]
  (require! (= :live (:status (header ctx w))) ::sealed {:world w})
  (require! (open? ctx w scope) ::closed-scope {:world w :scope scope})
  (let [current (current-run ctx w e)
        pred (when-not (= :unwinding (:status (read-row ctx w :runs current))) current)
        n (inc (max (or (second pred) 0)
                    (get-in (root-state ctx) [:generation-clock [w e]] 0)))
        r [e n]
        entry-reasons (reasons ctx w e)
        seqno (inc (max (get (header ctx w) :seq 0)
                        (get-in (root-state ctx) [:clocks w] 0)))]
    (require! (not= :inherited (:status (read-row ctx w :runs pred)))
              ::inherited-retirement-not-implemented {:w w :r pred})
    (root-edit! ctx assoc-in [:generation-clock [w e]] n)
    (header-edit! ctx w assoc :seq seqno)
    (put! ctx w :runs r {:spin e :owner scope :pred pred :status :running
                         :creations #{} :spawned #{} :seq seqno})
    (index-add! ctx w :runs-by-spin e r)
    (index-add! ctx w :runs-by-owner scope r)
    (when (read-row ctx w :runs scope)
      (edit! ctx w :runs scope update :spawned conj r))
    (emit! ctx {:event :body-entry :world w :e e :r r :cause cause
                :completed? (:completed? (read-row ctx w :entities e))
                :reasons entry-reasons
                :reachable? (boolean
                             (some (fn [[_ h]] (and (= e (:spin h)) (:reachable? h)
                                                    (contains? (:touched h) w)))
                                   (get-in (root-state ctx) [:env :handles])))})
    r))

(defn- move-run-owner! [ctx w r scope]
  (let [row (read-row ctx w :runs r)]
    (index-remove! ctx w :runs-by-owner (:owner row) r)
    (edit! ctx w :runs r assoc :owner scope)
    (index-add! ctx w :runs-by-owner scope r)))

(defn- create-spin! [ctx {:keys [w e tok order] :or {order 0} :as action}]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (let [scope (owner ctx w action)
        rr (read-row ctx w :runs scope)
        old (read-row ctx w :entities e)
        adopt? (and rr old (predecessor? ctx w (:creator old) scope))
        h (get-in (root-state ctx) [:env :handles tok])]
    (when h (require! (= e (:spin h)) ::token-spin-mismatch {:tok tok :e e :handle h}))
    (when (and tok (nil? h))
      (root-edit! ctx assoc-in [:env :handles tok]
                  {:spin e :reachable? true :touched #{} :dropped #{}}))
    (when (and rr (or (nil? old) adopt?))
      (put-entity! ctx w e
                   (merge (or old (spin-row ctx w e scope))
                          {:owner scope :creator scope :kept? (reactive? ctx w scope) :order order}))
      (edit! ctx w :runs scope update :creations conj e))
    (when adopt?
      (doseq [r (read-row ctx w :runs-by-spin e)
              :when (= (:creator old) (:owner (read-row ctx w :runs r)))]
        (move-run-owner! ctx w r scope)))
    (touch! ctx w e tok)))

(defn- reenter! [ctx {:keys [w e cause order] :or {cause :dirty order -1}}]
  (require! (= :live (:status (header ctx w))) ::not-live {:world w})
  (let [r (current-run ctx w e)
        rr (read-row ctx w :runs r)
        work? (#{:running :parked} (:status rr))]
    (require! rr ::missing-run {:e e})
    (doseq [p (read-row ctx w :runs-by-spin e)
            :when (= :stale (:status (read-row ctx w :runs p)))]
      (supersede! ctx w p))
    (let [r2 (start-run! ctx w e (:owner rr) cause)]
      (when work?
        (edit! ctx w :runs r assoc :status :stale))
      (doseq [o (read-row ctx w :by-creditor [:run w r])
              :let [ob (read-row ctx w :obligations o)]]
        (if (and work? (= :track (:kind ob)) (<= (:order ob) order))
          (do (index-remove! ctx w :by-creditor [:run w r] o)
              (edit! ctx w :obligations o assoc :creditor [:run w r2])
              (index-add! ctx w :by-creditor [:run w r2] o))
          (when work? (end-obligation! ctx w o :creditor-cancelled))))
      (doseq [child (:creations rr)
              :when (< (get (read-row ctx w :entities child) :order 0) order)]
        (put-entity! ctx w child (assoc (read-row ctx w :entities child) :owner r2 :creator r2))
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
      (when (nil? (:owner (read-row ctx w :entities e)))
        (put-entity! ctx w e (assoc (read-row ctx w :entities e) :owner scope)))
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
              (add-obligation! ctx dw o ob))))))))

(defn- register! [ctx {:keys [w r kind debtor tok order recovery]
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
        er (when (= dk :entity) (read-row ctx dw :entities e))
        await? (and (= dk :entity) (#{:await-once :await-reactive} kind))
        work? (some #(#{:running :parked} (:status (read-row ctx dw :runs %)))
                    (read-row ctx dw :runs-by-spin e))
        foreign-cold? (and await? (not= w dw) (not work?) (not (:completed? er)))]
    (require! (or (not= dk :entity) er foreign-cold?) ::missing-debtor {:debtor debtor})
    (when (and await? (= w dw) (not work?) (not (:completed? er)))
      (start-run! ctx w e r :await))
    (if (and (= kind :await-once) (:completed? er))
      (emit! ctx {:event :inline-resume :world w :r r})
      (let [o (allocate! ctx :o)
            token [:cancel o]
            ob {:kind kind :debtor debtor :creditor [:run w r]
                :standing? (boolean (#{:track :await-reactive :callback} kind))
                :cont [:continuation o] :token (when (= kind :external) token)
                :order order :origin :created
                :slot (if (= kind :track) :consumed :armed)}]
        (edit! ctx w :runs r assoc :status (if (= kind :track) :running :parked))
        (add-obligation! ctx w o ob)
        (if foreign-cold?
          (enqueue! ctx dw {:start-for e :creditor-world w :o o :tok tok})
          (when (and (= dk :entity) (not= w dw))
            (header-edit! ctx dw update :fdeps conj [e w o])))
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
          (when-not foreign-cold? (touch! ctx dw e tok)))))))

(defn- resume! [ctx {:keys [w o value] :or {value :value}}]
  (when-let [ob (read-row ctx w :obligations o)]
    (let [[ck _ r] (:creditor ob)
          rr (read-row ctx w :runs r)]
      (when (and (= :armed (:slot ob)) (= ck :run) (= :inherited (:status rr)))
        (require! false ::inherited-activation-not-implemented {:w w :o o}))
      (when (and (= :armed (:slot ob)) (= ck :run) (= :parked (:status rr)))
        (if (:standing? ob)
          (edit! ctx w :obligations o assoc :slot :consumed)
          (end-obligation! ctx w o :delivered))
        (edit! ctx w :runs r assoc :status :running)
        (emit! ctx {:event :resume :world w :r r :o o
                    :one-shot? (not (:standing? ob))
                    :thread-world w :value value})))))

(defn- complete! [ctx {:keys [w r value] :or {value :result}}]
  (let [rr (read-row ctx w :runs r)
        e (:spin rr)]
    (when (and (= :running (:status rr)) (= r (current-run ctx w e)))
      (edit! ctx w :entities e assoc :completed? true :dirty? false :result value)
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
  (let [dw (or debtor-world w)
        ids (read-row ctx w :by-debtor [:entity dw e])]
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
        (if (:standing? ob)
          (reenter! ctx {:w w :e (first (nth (:creditor ob) 2))
                         :cause (if (= :track (:kind ob)) :track :reactive)
                         :order (:order ob)})
          (resume! ctx {:w w :o o :value value}))))))

(defn step!
  "Execute a supported transition, returning delivery descriptors after commit.
  Unsupported actions refuse explicitly; this is not yet the runtime engine."
  [kernel {:keys [t w o] :as action}]
  (store/transact!
   kernel
   (fn [tx]
     (let [ctx {:tx tx :events (volatile! []) :work (volatile! [])}
           thread (get-in (root-state ctx) [:env :threads (:th action)])
           slice? (:run thread)
           unwinding? (= :unwinding (:status (read-row ctx (:world thread) :runs (:run thread))))
           action (if (and slice? (not (#{:t38 :slice-enter :t35} t)))
                    (assoc action :w (:world thread)) action)
           w (:w action)]
       (when (and slice? (not= :t38 t) (= :released (:status (header ctx (:world thread)))))
         (require! false ::released {:w w :thread (:th action)}))
       (when (and unwinding? (#{:t01 :t02 :t03 :t04 :t05 :t12 :t19 :t20 :t20q} t))
         (require! false ::cancelled {:w w :r (:run thread)}))
       (case t
         :t01 (create-spin! ctx action)
         :t02
         (create-source! ctx action)
         :t04 (invoke! ctx action)
         :t03
         (let [r (:r action)
               rr (read-row ctx w :runs r)]
           (require! (#{:running :parked} (:status rr)) ::not-work {:r r})
           (put-entity! ctx w [(:spin rr) (:key action)]
                        (entity-row (get action :kind :cache-row) r)))
         :t12
         (do (require! (= :live (:status (header ctx w))) ::not-live {:world w})
             (require! (open? ctx w (:parent action)) ::closed-scope {:parent (:parent action)})
             (put! ctx w :scopes (:scope action)
                   {:kind (get action :kind :explicit) :parent (:parent action) :status :open})
             (index-add! ctx w :scopes-by-parent (:parent action) (:scope action)))
         :t05 (register! ctx action)
         :t06 (resume! ctx action)
         :t07 (complete! ctx action)
         :t08 (deliver! ctx action)
         :t09 (reenter! ctx action)
         :t10 (supersede! ctx w (:r action))
         :t11 (cancel-run! ctx w (:r action) (:anchor action))
         :t13 (close-scope! ctx w (:scope action))
         :t15
         (doseq [[r rr] (store/table-view tx w :runs)
                 :when (#{:running :parked} (:status rr))]
           (cancel-run! ctx w r nil))
         :slice-enter
         (let [th (:th action) r (:r action)]
           (require! (= :running (:status (read-row ctx w :runs r))) ::not-running {:w w :r r})
           (require! (nil? (get-in (root-state ctx) [:env :threads th :run])) ::thread-busy {:th th})
           (require! (not-any? #(and (= w (:world %)) (= r (:run %)))
                               (vals (get-in (root-state ctx) [:env :threads])))
                     ::slice-busy {:w w :r r})
           (root-edit! ctx update-in [:env :threads th] merge
                       {:world w :scope r :run r :obligation-world w :executing? true}))
         :t38
         (let [th (:th action)
               {:keys [world run]} (get-in (root-state ctx) [:env :threads th])]
           (require! run ::no-slice {:th th})
           (root-edit! ctx update-in [:env :threads th]
                       #(-> % (assoc :run nil :scope nil :executing? false)
                            (dissoc :retired? :obligation-world)))
           (when (and (= :unwinding (:status (read-row ctx world :runs run)))
                      (not (physical? ctx world run)))
             (remove-run! ctx world run)))
         :native-progress
         (let [[world run] (get-in (root-state ctx) [:env :native (:n action) :owner])]
           (root-edit! ctx update-in [:env :native (:n action)] merge (select-keys action [:state :boundary?]))
           (when (and (= :unwinding (:status (read-row ctx world :runs run)))
                      (not (physical? ctx world run)))
             (remove-run! ctx world run)))
         :thread-entry
         (do (require! (nil? (get-in (root-state ctx) [:env :threads (:th action) :run]))
                       ::thread-busy {:th (:th action)})
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
             (enqueue! ctx w {:completion e :debtor-world w :value (:value action)})
             (doseq [v (set (for [[x v d] (:fdeps (header ctx w))
                                  :when (if (= :bundle x) (contains? d e) (= x e))] v))]
               (enqueue! ctx v {:completion e :debtor-world w :value (:value action)}))))
         :unsubscribe
         (let [ob (read-row ctx w :obligations o)]
           (require! (or (nil? ob) (:standing? ob)) ::not-standing {:o o})
           (end-obligation! ctx w o :creditor-cancelled))
         (throw (ex-info "Unsupported kernel transition" {:action action})))
       (rule-l! ctx)
       (root-edit! ctx assoc :events @(:events ctx))
       @(:events ctx)))))
