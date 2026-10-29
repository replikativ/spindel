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
            :entities-by-owner (reduce-kv #(index-add %1 (:owner %3) %2) {} (:entities world))})))

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

(defn- put! [ctx w table id value]
  (store/put-row! (:tx ctx) w table id value))

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
    (store/delete-row! (:tx ctx) w :obligations o)
    (index-remove! ctx w :by-creditor (:creditor ob) o)
    (index-remove! ctx w :by-debtor (:debtor ob) o)
    (emit! ctx {:event :obligation-exit :world w :o o :ob ob :cause cause})
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
  (let [pred (current-run ctx w e)
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
          (put! ctx w :entities [:timer o]
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

(defn step!
  "Execute a supported transition, returning delivery descriptors after commit.
  Unsupported actions refuse explicitly; this is not yet the runtime engine."
  [kernel {:keys [t w o] :as action}]
  (store/transact!
   kernel
   (fn [tx]
     (let [ctx {:tx tx :events (volatile! [])}]
       (case t
         :t02
         (create-source! ctx action)
         :t04 (invoke! ctx action)
         :t12
         (do (require! (= :live (:status (header ctx w))) ::not-live {:world w})
             (require! (open? ctx w (:parent action)) ::closed-scope {:parent (:parent action)})
             (put! ctx w :scopes (:scope action)
                   {:kind (get action :kind :explicit) :parent (:parent action) :status :open}))
         :t05 (register! ctx action)
         :t06 (resume! ctx action)
         :unsubscribe
         (let [ob (read-row ctx w :obligations o)]
           (require! (or (nil? ob) (:standing? ob)) ::not-standing {:o o})
           (end-obligation! ctx w o :creditor-cancelled))
         (throw (ex-info "Unsupported kernel transition" {:action action})))
       (root-edit! ctx assoc :events @(:events ctx))
       @(:events ctx)))))
