(ns org.replikativ.spindel.lifetime.model
  "Executable Part 4, independent of src/. Actions are maps with :t and arguments.
  Expanded logical rows; physical attach cost is outside this model."
  (:require [clojure.set :as set]
            [clojure.walk :as walk]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.lifetime.lifecycle :as lifecycle]
            [org.replikativ.spindel.lifetime.managed-cells :as managed-cells]))

(def terminal #{:merged :discarded :transferred :partitioned})
(def ^:dynamic *release-cancellation* nil)

(def standing #{:track :await-reactive :callback})
(def work-status #{:running :parked})
(def active-cuts #{:fenced :ready :captured :attached})
(def defaults {:worlds 3 :world-ids 4 :invocations 2 :host-registrations 2 :spins 4 :generations 2 :scopes 2 :scope-births 3 :handles 2
               :custody-orders [1 2] :steps 2 :cuts 2 :depth 40 :crashes 1 :failures 1 :unknowns 1 :writes 1
               :threads 2 :slice-enters 1 :registrations 1 :signals 1 :atoms 1 :filters [:local :causal-follow] :invoke-modes [:deref :callback] :durable-systems #{:a :b}})

(defn world-row [w parent mode root]
  {:id w :lineage {:parent parent :root root :mode mode :cut nil :basis nil}
   :status :live :admission :open :seal-seq nil :root [:root w]
   :next-scope 0 :scope-balance 0
   :scopes {[:root w] {:kind (if parent :fork :world-root) :parent nil :status :open}}
   :entities {} :runs {} :obligations {} :releasing #{} :fdeps #{} :pins #{} :queue []})

(defn init-state
  "§4.1. A single selected root world; options set search bounds and registered durable systems."
  ([] (init-state {}))
  ([options]
   (let [w [:w 0]]
     {:worlds {w (world-row w nil :root w)} :registry #{w} :cuts {}
      :caps {} :records {} :durable {:caps {} :records {}}
      :custody {:by-holder {} :claims {}} :next-claim 0 :recovery-epoch 0 :process-live? true
      :env {:handles {} :threads {:host {:world w :scope nil :run nil
                                         :read-permits #{} :excl-permits []}}
            :native {} :outside [] :principals (get options :external-principals #{})}
      ;; Instrumentation is data, never a retention reason.
      :model (merge defaults options) :serial {} :events []
      :known-worlds #{w} :lineages {w (:lineage (world-row w nil :root w))}
      :adapter-effects #{} :freed-bases #{} :restarted? false})))

(defn refuse [error data] (throw (ex-info (name error) (assoc data :error error))))
(defn require! [p error data] (when-not p (refuse error data)))
(defn fresh [s tag] [tag (get-in s [:serial tag] 0)])
(defn allocate [s tag] [(update-in s [:serial tag] (fnil inc 0)) (fresh s tag)])
(defn wr [s w] (get-in s [:worlds w]))
(defn ent [s w e] (get-in s [:worlds w :entities e]))
(defn run [s w r] (get-in s [:worlds w :runs r]))
(defn work? [r] (boolean (work-status (:status r))))
(defn busy? [r] (or (work? r) (= :unwinding (:status r))))
(defn cut-busy? [r] (and (busy? r) (not= :parked (:status r))))
(defn explicit-scope-id? [id]
  (and (vector? id) (= 3 (count id)) (= [:scope :id] (subvec id 0 2))
       (integer? (nth id 2)) (not (neg? (nth id 2)))))

(defn open? [s w scope]
  (or (and (run s w scope) (not= :unwinding (:status (run s w scope))))
      (= :open (get-in s [:worlds w :scopes scope :status]))))
(defn current [s w e]
  (last (sort-by second (for [[r row] (:runs (wr s w)) :when (= e (:spin row))] r))))
(def ^:dynamic *retiring-owners* {})

(defn owner-chain [s w r]
  (loop [id r chain [] seen #{}]
    (cond
      (nil? id) (conj chain w)
      (contains? *retiring-owners* [w id]) (into chain (get *retiring-owners* [w id]))
      (seen id) chain
      (= :unwinding (:status (run s w id))) (into chain (:anchor (run s w id)))
      :else (recur (or (:owner (run s w id))
                       (get-in s [:worlds w :scopes id :parent]))
                   (conj chain id) (conj seen id)))))
(defn physical? [s w r]
  (or (some #(and (= w (:world %)) (= r (:run %))) (vals (get-in s [:env :threads])))
      (some #(and (= [w r] (:owner %)) (not (cleanup/mailbox-callback? %)) (not= :joined (:state %))) (vals (get-in s [:env :native])))))
(defn join-blockers [s w x]
  (let [released? (= :released (:status (wr s w)))
        physical-under? (fn [r participant]
                          (if (or released? (cleanup/mailbox-callback? participant))
                            (or (= x w) (= x r) (some #{x} (:anchor participant)))
                            (some #{x} (owner-chain s w r))))]
    (vec (distinct
          (concat
           (when-not released?
             (for [[r rr] (:runs (wr s w))
                   :when (and (busy? rr) (some #{x} (owner-chain s w r)))] r))
           ;; A completed or stale row can still have a physical participant.
           ;; Joining must not depend on a later delivery/normalization turning
           ;; that row into :unwinding first.
           (for [[_ thread] (get-in s [:env :threads]) :let [r (:run thread)]
                 :when (and r (= w (:world thread)) (physical-under? r thread))] r)
           (for [[_ native] (get-in s [:env :native]) :let [[world r] (:owner native)]
                 :when (and (= w world) (not= :joined (:state native))
                            (physical-under? r native))] r))))))
(defn join-ready? [s w x]
  (empty? (join-blockers s w x)))

(defn reactive? [s w r]
  (boolean (some (fn [[_ o]] (and (= [:run w r] (:creditor o))
                                  (:standing? o) (#{:track :await-reactive} (:kind o))))
                 (:obligations (wr s w)))))
(defn final? [s w e]
  (and (:completed? (ent s w e)) (not (reactive? s w (current s w e)))))
(defn quiescent? [s w]
  (and (not-any? busy? (vals (:runs (wr s w))))
       (not-any? #(and (#{:timer :external} (:kind %))
                       (not= :inherited (:status (run s w (nth (:creditor %) 2 nil)))))
                 (vals (:obligations (wr s w))))))
(defn joined? [s w]
  (and (not-any? #(and (= w (:world %)) (:run %))
                 (vals (get-in s [:env :threads])))
       (every? #(or (not= w (first (:owner %))) (= :joined (:state %)))
               (vals (get-in s [:env :native])))))
(defn all-caps [s] (merge (:caps s) (get-in s [:durable :caps])))
(defn all-records [s] (merge (:records s) (get-in s [:durable :records])))
(defn cap [s k] (get (all-caps s) k))
(defn vanished-caps
  "Value-only terminal authority from partition descriptors; never runtime caps."
  [s]
  (into {} (for [[op rec] (get-in s [:durable :records]) desc (:successors rec)
                 :when (:vanished? desc)]
             [(:k desc) (assoc desc :world (:world (cap s (:cap rec))) :pred (:cap rec) :op op)])))
(defn record [s op] (get (all-records s) op))
(defn durable-scope? [s scope]
  (boolean (seq (set/intersection scope (get-in s [:model :durable-systems])))))
(defn cap-path [s k] (if (get-in s [:durable :caps k]) [:durable :caps k] [:caps k]))
(defn record-path [s op]
  (if (get-in s [:durable :records op]) [:durable :records op] [:records op]))
(defn execution-holder [w owner]
  [:execution-owner w (cond (= owner [:root w]) :root
                            (explicit-scope-id? owner) :scope
                            :else :run) owner])
(defn holder-ref? [holder]
  (and (vector? holder)
       (case (first holder)
         :execution-owner (and (= 4 (count holder))
                               (case (nth holder 2)
                                 :root (= (nth holder 3) [:root (second holder)])
                                 :scope (explicit-scope-id? (nth holder 3))
                                 :run (and (vector? (nth holder 3)) (= 2 (count (nth holder 3))))
                                 false))
         :external (= 2 (count holder))
         :cleanup (= 2 (count holder))
         :recovery (= 3 (count holder))
         false)))
(defn holder-open? [s holder]
  (and (holder-ref? holder)
       (case (first holder)
         :execution-owner
         (let [[_ w kind id] holder rr (run s w id)]
           (and (wr s w) (not= :released (:status (wr s w)))
                (if (= :run kind)
                  (and rr (= id (current s w (:spin rr)))
                       (or (#{:running :parked} (:status rr))
                           (and (= :completed (:status rr)) (reactive? s w id))))
                  (open? s w id))))
         :external (contains? (get-in s [:env :principals] #{}) holder)
         :cleanup (contains? (get-in s [:custody :claims]) (second holder))
         :recovery (and (:restarted? s) (= holder [:recovery :durable (:recovery-epoch s)]))
         false)))
(defn remove-custody [s k holder]
  (let [members (disj (get-in s [:custody :by-holder holder] #{}) k)]
    (if (seq members) (assoc-in s [:custody :by-holder holder] members)
        (update-in s [:custody :by-holder] dissoc holder))))
(defn put-cap [s k c]
  (let [old (cap s k) d (durable-scope? s (:scope c))
        s (if (and old (not (terminal (:disposition old))))
            (remove-custody s k (:holder old)) s)]
    (cond-> (-> s (update :caps dissoc k) (update-in [:durable :caps] dissoc k)
                (assoc-in (if d [:durable :caps k] [:caps k]) (assoc c :durable? d)))
      (not (terminal (:disposition c)))
      (update-in [:custody :by-holder (:holder c)] (fnil conj #{}) k))))
(defn remove-cap [s k]
  (let [c (cap s k)]
    (-> (remove-custody s k (:holder c))
        (update :caps dissoc k) (update-in [:durable :caps] dissoc k))))
(defn fresh-cap! [s k]
  (require! (and k (nil? (cap s k)) (nil? (get (vanished-caps s) k))
                 (not-any? #(some (fn [desc] (= k (:k desc))) (:successors %)) (vals (all-records s))))
            ::cap-id-reused {:k k}))
(defn terminal-custody-envelope? [s w event]
  (let [c (cap s (:cap event)) rec (record s (:op event))]
    (and (#{:merged :discarded} (:disposition c)) (= w (:world c))
         (= [:cleanup (:custody-dispatch event)] (:holder c))
         (= (:op event) (:op c)) (= (:cap event) (:cap rec)))))

(defn operation-fresh?
  "All committed/reserved operation domains; only dispatch may reuse its own claim."
  [s op exempt-claim]
  (and (some? op) (not (contains? (all-records s) op))
       (not-any? #(= op (:op %)) (vals (all-caps s)))
       (not-any? (fn [[id claim]] (and (not= id exempt-claim) (= op (:settlement-op claim))))
                 (get-in s [:custody :claims]))))
(defn fresh-operation!
  ([s op] (fresh-operation! s op nil))
  ([s op exempt-claim]
   (require! (operation-fresh? s op exempt-claim) ::op-exists {:op op})))
(defn allocate-custody-claim [s c]
  (loop [n (:next-claim s)]
    (let [id [:custody-claim n] op (if (= :open (:disposition c)) [:custody-op id] (:op c))]
      (if (and (not (contains? (get-in s [:custody :claims]) id))
               (or (not= :open (:disposition c)) (operation-fresh? s op nil)))
        [(assoc s :next-claim (inc n)) id op]
        (recur (inc n))))))
(defn fresh-recovery-operation [s k]
  (loop [n 0]
    (let [op [:recovery-op (:recovery-epoch s) k n]]
      (if (operation-fresh? s op nil) op (recur (inc n))))))

(defn authenticate-holder! [s k caller]
  (let [c (cap s k)]
    (require! (and (= caller (:holder c)) (holder-open? s caller))
              ::stale-capability {:k k :caller caller})))
(defn holder-acquisition! [s holder acceptance]
  (require! (and (holder-open? s holder) (#{:execution-owner :external} (first holder)))
            ::invalid-destination {:holder holder})
  (if (= :execution-owner (first holder))
    (let [[_ w kind id] holder rr (run s w id)]
      (if (= :run kind)
        (if (= :running (:status rr))
          (let [{:keys [th order]} acceptance thread (get-in s [:env :threads th])]
            (require! (and (= w (:world thread)) (= id (:run thread)) (:executing? thread)
                           (not (:retired? thread)) (nil? (:cleanup-ticket thread))
                           (integer? order) (not (neg? order)))
                      ::missing-destination-order {:holder holder :acceptance acceptance})
            order)
          :exact-run)
        nil))
    nil))

(defn accept-holder! [s holder acceptance]
  (require! (holder-ref? holder) ::invalid-destination {:holder holder})
  (when (= :execution-owner (first holder))
    (let [w (second holder)]
      (require! (and (= :live (:status (wr s w))) (= :open (:admission (wr s w))))
                ::invalid-destination {:holder holder})))
  (holder-acquisition! s holder acceptance))

(defn custody-actors
  "Admitted model actors, independently of the cap whose authority is requested."
  [s]
  (filter #(holder-open? s %)
          (concat (get-in s [:env :principals])
                  (when (:restarted? s) [[:recovery :durable (:recovery-epoch s)]])
                  (map :holder (vals (get-in s [:custody :claims])))
                  (for [[w world] (:worlds s) owner (concat (keys (:scopes world)) (keys (:runs world)))]
                    (execution-holder w owner)))))

(defn custody-destinations [s]
  (concat
   (for [principal (get-in s [:env :principals])]
     {:holder principal :acceptor principal})
   (for [[w world] (:worlds s) :when (and (= :live (:status world)) (= :open (:admission world)))
         owner (concat (keys (:scopes world)) (keys (:runs world)))
         :let [holder (execution-holder w owner)] :when (holder-open? s holder)
         acceptance (if (= :running (:status (run s w owner)))
                      (for [[th thread] (get-in s [:env :threads])
                            :when (and (= w (:world thread)) (= owner (:run thread)) (:executing? thread)
                                       (not (:retired? thread)) (nil? (:cleanup-ticket thread)))
                            order (get-in s [:model :custody-orders])]
                        {:th th :order order})
                      [nil])]
     (cond-> {:holder holder :acceptor holder} acceptance (assoc :acceptance acceptance)))))

(defn fdep-targets [world e]
  (set (for [[x v d] (:fdeps world) :when (if (= :bundle x) (contains? d e) (= x e))] v)))
(def ^:dynamic *liveness-cache* nil)
(def ^:dynamic *cache-gc-only?* false)
(declare cancelling? pending-events)

(defn- compute-rooted-liveness [s]
  (let [edges (volatile! {}) roots (volatile! #{})
        edge! (fn [from to] (vswap! edges update from (fnil conj #{}) to))
        root! #(vswap! roots conj %)
        owner (fn [w id] [(if (run s w id) :run :scope) w id])]
    (doseq [[w world] (:worlds s) :when (not= :released (:status world))]
      (root! [:scope w (:root world)])
      (doseq [[id scope] (:scopes world) :when (= :open (:status scope))
              :let [parent (:parent scope)] :when parent]
        (edge! (owner w parent) [:scope w id])
        (edge! [:scope w id] (owner w parent)))
      (doseq [[e er] (:entities world) :let [v [:entity w e] p (:owner er)]]
        (when p
          (edge! v (owner w p))
          (when (and (open? s w p)
                     (or (#{:signal :atom :deferred :mailbox :keyed-entry :cache-row :fork} (:kind er))
                         (and (= :spin (:kind er)) (or (not (:completed? er)) (:kept? er)))
                         (and (#{:timer :waiter} (:kind er))
                              (#{:running :parked :inherited} (:status (run s w p))))))
            (edge! (owner w p) v)))
        (when (or (contains? (:pins world) e)
                  (and (= :fork (:kind er)) (not (:reference? er))
                       (some #(and (= (second e) (:world %))
                                   (#{:sealed :settling :incomplete} (:disposition %)))
                             (vals (all-caps s)))))
          (root! v)))
      (doseq [[r rr] (:runs world) :let [v [:run w r] e [:entity w (:spin rr)]]]
        (when (#{:running :parked :inherited :stale} (:status rr)) (root! v))
        (when-not (= :unwinding (:status rr))
          (edge! v e) (edge! e v)
          (when-let [p (:owner rr)]
            (edge! v (owner w p)))))
      (doseq [[o ob] (:obligations world)
              :let [v [:obligation w o] [ck cw creditor] (:creditor ob)
                    [dk dw debtor] (:debtor ob)]]
        (case ck
          :host (root! v)
          :run (edge! [:run cw creditor] v)
          :entity (edge! [:entity cw creditor] v)
          nil)
        (when (and (= :entity dk) (not (cancelling? s w o ob)))
          (edge! v [:entity dw debtor])))
      (doseq [ev (:queue world) :when (:register-host ev)]
        (root! [:entity w (:e ev)])))
    (doseq [{:keys [w event]} (get-in s [:env :outside]) :when (:register-host event)]
      (root! [:entity w (:e event)]))
    (loop [todo (vec @roots) seen #{}]
      (if-let [v (peek todo)]
        (recur (if (contains? seen v) (pop todo) (into (pop todo) (get @edges v))) (conj seen v))
        seen))))

(defn rooted-liveness
  "Least retention closure. Handles and foreign index mirrors are not execution
  roots; foreign dependencies still retain storage until their local ACK."
  [s]
  (if *liveness-cache*
    (let [[before result] @*liveness-cache*]
      (if (identical? before s) result
          (let [result (compute-rooted-liveness s)]
            (vreset! *liveness-cache* [s result]) result)))
    (compute-rooted-liveness s)))

(defn execution-live? [s w e]
  (contains? (rooted-liveness s) [:entity w e]))

(defn reasons [s w e]
  (let [{:keys [kind owner completed? kept? reference?]} (ent s w e)
        world (wr s w) live (rooted-liveness s)
        entity-live? (contains? live [:entity w e])]
    (cond-> #{}
      ;; Storage survives until the owner's world publishes its cleanup.
      ;; This reason never contributes an execution root.
      (or (and owner (open? s w owner)
               (not (or (contains? live [:run w owner])
                        (contains? live [:scope w owner]))))
          (some (fn [[r rr]]
                  (and (= e (:spin rr)) (not= :unwinding (:status rr))
                       (not (contains? live [:run w r]))))
                (:runs world))) (conj :extent)
      (and entity-live? owner (open? s w owner)
           (or (#{:signal :atom :deferred :mailbox :keyed-entry :cache-row :fork} kind)
               (and (#{:timer :waiter} kind) (#{:running :parked :inherited} (:status (run s w owner))))
               (and (= :spin kind) (or (not completed?) kept?)))) (conj :own)
      (some #(and (= e (:spin %))
                  (#{:running :parked :inherited :stale} (:status %)))
            (vals (:runs world))) (conj :active)
      (or (some (fn [[o ob]] (and (contains? live [:obligation w o])
                                  (some #{[:entity w e]} [(:debtor ob) (:creditor ob)])))
                (:obligations world))
          (some #(and (:register-host %) (= e (:e %))) (pending-events s w))) (conj :obl)
      (seq (fdep-targets (update world :fdeps set/union (:releasing world)) e)) (conj :dep)
      (some (fn [[r rr]]
              (and (= e (:spin rr)) (= :completed (:status rr))
                   (contains? live [:run w r])
                   (or (some (fn [[child cr]]
                               (and (= r (:owner cr)) (not= :unwinding (:status cr))
                                    (contains? live [:run w child]))) (:runs world))
                       (some (fn [[child er]] (and (= r (:owner er)) (not= child e)
                                                   (contains? live [:entity w child])))
                             (:entities world))))) (:runs world)) (conj :scope)
      (contains? (:pins world) e) (conj :pin)
      (and (= :fork kind) (not reference?)
           (some #(and (= (second e) (:world %))
                       (#{:sealed :settling :incomplete} (:disposition %)))
                 (vals (all-caps s)))) (conj :settle))))
(defn idle? [s w e]
  (and (= :spin (:kind (ent s w e))) (:completed? (ent s w e))
       (empty? (reasons s w e))))
(defn keyid [s w k] [:key (get-in s [:worlds w :lineage :root]) k])
(defn emit [s event] (update s :events conj event))
(defn selected [s {:keys [th w] :or {th :host}}]
  (or w (get-in s [:env :threads th :world]) (refuse ::no-world {:thread th})))
(defn cs [s a w]
  (let [th (get-in s [:env :threads (get a :th :host)])]
    (or (:scope a) (:scope th) (:r a) (:run th) (:root (wr s w)))))
(defn live! [s w]
  (require! (= :live (:status (wr s w))) ::not-live {:world w})
  (require! (not-any? #(and (= w (:child %)) (= :attached (:phase %))) (vals (:cuts s)))
            ::not-admitted {:world w}))
(defn row [kind owner]
  {:kind kind :origin :created :owner owner :creator nil :completed? false
   :kept? false :result nil :tokens #{} :key nil :order 0})
(defn caps-of [s w] (filter #(= w (:world (val %))) (all-caps s)))
(defn predecessor? [s w old r]
  (contains? (:ancestors (run s w r)) old))

(defn prune-ancestry [s w]
  (let [world (wr s w)
        relevant (into (set (for [[r rr] (:runs world) :when (not= :unwinding (:status rr))] r)) (keep :creator (vals (:entities world))))]
    (update-in s [:worlds w :runs]
               #(into {} (for [[r rr] %]
                           [r (update rr :ancestors (fn [ids] (set (filter relevant ids))))])))))

(defn touch [s w e tok]
  (if (and tok (ent s w e))
    (-> s (update-in [:worlds w :entities e :tokens] (fnil conj #{}) tok)
        (update-in [:env :handles tok :touched] (fnil conj #{}) w)) s))

(defn covering-tokens [s w e]
  (set (for [[tok h] (get-in s [:env :handles])
             :when (and (= e (:spin h)) (:reachable? h)
                        (contains? (:touched h) w) (not (contains? (:dropped h) w)))] tok)))

(defn spin-row [s w e owner]
  (assoc (row :spin owner) :tokens (covering-tokens s w e)))

(defn pending-events [s w]
  (concat (:queue (wr s w))
          (map :event (filter #(= w (:w %)) (get-in s [:env :outside])))))

(defn cut-participant? [s w]
  (some #(and (active-cuts (:phase %))
              (contains? (get-in % [:participants :worlds]) w)) (vals (:cuts s))))

(defn quiescent-cut? [s w]
  (some #(and (= :p1q (:protocol %)) (active-cuts (:phase %))
              (contains? (get-in % [:participants :worlds]) w)) (vals (:cuts s))))

(defn pending-request? [s v o ob]
  (let [[kind w e] (:debtor ob)]
    (and (= :entity kind) (not= w v)
         (some #(or (and (= e (:start-for %)) (= v (:creditor-world %)) (= o (:o %)))
                    (and (= v (:join-bundle %)) (= e (get-in % [:members o :debtor]))))
               (pending-events s w)))))

(defn attached-pending? [s v o ob]
  (some (fn [[_ cut]]
          (and (= :attached (:phase cut)) (= v (:child cut))
               (= :inherited (:status (run s v (nth (:creditor ob) 2 nil))))
               (some #(#{:admitted :pending-start} (get-in % [:copy-evidence o :phase]))
                     (vals (:basis cut)))))
        (:cuts s)))

(defn pending-start? [s v o ob]
  (let [[kind w _] (:debtor ob)]
    (and (= :entity kind) (not= w v)
         (or (attached-pending? s v o ob) (pending-request? s v o ob)))))

(defn known-foreign-obligation? [s w v o ob]
  ;; A debtor knows only its own dependency rows and request envelopes.
  (let [e (nth (:debtor ob) 2)]
    (or (pending-request? s v o ob)
        (contains? (:fdeps (wr s w)) [e v o])
        (some (fn [[tag target d]]
                (and (= :bundle tag) (= v target) (contains? d e)))
              (:fdeps (wr s w))))))

(defn cancelling? [s v o ob]
  (and (= :entity (first (:debtor ob))) (not= v (second (:debtor ob)))
       (some #(= o (:cancelled %)) (pending-events s v))))

(defn control-key [event]
  (if (:start-for event) [:start-for (:creditor-world event) (:o event)]
      (first (for [k [:custody-dispatch :cancelled :register-host :fdep-ended :fork-released :join-bundle]
                   :when (contains? event k)] [k (get event k)]))))

(defn source-notification-key [event]
  ;; Provenance survives debtor release. Never infer conflation eligibility
  ;; from the current entity row or apply it to first-result completions.
  (when (:source-change? event) [(:debtor-world event) (:completion event)]))

(defn append-notification [events event]
  (if-let [key (source-notification-key event)]
    (conj (vec (remove #(= key (source-notification-key %)) events)) event)
    (conj events event)))

(defn enqueue
  "Tombstone requests fail locally in the sender transaction; joins reject every member."
  [s w event]
  (cond
    (= :released (:status (wr s w)))
    (cond (:join-bundle event) (reduce #(enqueue %1 (:join-bundle event) {:cancelled %2 :value ::released})
                                       s (keys (:members event)))
          (:start-for event) (enqueue s (:creditor-world event) {:cancelled (:o event) :value ::released})
          (:register-host event) (emit s {:event :host-delivery :world w
                                          :o (:register-host event) :value ::released})
          :else s)
    (and (control-key event)
         (some #(= (control-key event) (control-key %)) (pending-events s w)))
    (if (:value event)
      (-> s (update-in [:worlds w :queue]
                       #(mapv (fn [queued] (if (= (control-key event) (control-key queued))
                                             (merge queued event) queued)) %))
          (update-in [:env :outside]
                     #(mapv (fn [held] (if (and (= w (:w held))
                                                (= (control-key event) (control-key (:event held))))
                                         (update held :event merge event) held)) %))) s)
    :else
    (let [n (inc (max (get-in s [:worlds w :seq] 0) (get-in s [:clocks w] 0)))
          event (assoc event :seq n) s (assoc-in s [:clocks w] n)]
      (if (and (= :fenced (:admission (wr s w))) (or (cut-participant? s w) (not (control-key event))))
        (update-in s [:env :outside]
                   (fn [held]
                     (let [key (source-notification-key event)]
                       (conj (if key
                               (vec (remove #(and (= w (:w %))
                                                  (= key (source-notification-key (:event %)))) held))
                               held)
                             {:w w :event event}))))
        (update-in s [:worlds w :queue] append-notification event)))))

(defn cleanup-dependency [s dw fd _creditor-world]
  (if (or (= :released (:status (wr s dw)))
          (contains? (:releasing (wr s dw)) fd)) s
      (-> s (update-in [:worlds dw :fdeps] disj fd)
          (update-in [:worlds dw :releasing] conj fd)
          (enqueue dw {:fdep-ended fd}))))

(defn sync-bundle [s dw v]
  (let [old (first (filter #(and (= :bundle (first %)) (= v (second %))) (:fdeps (wr s dw))))
        d (set (for [[o ob] (:obligations (wr s v))
                     :when (and (= :entity (first (:debtor ob))) (= dw (second (:debtor ob)))
                                (= :run (first (:creditor ob)))
                                (not (pending-start? s v o ob)) (not (cancelling? s v o ob))
                                (= :inherited (:status (run s v (nth (:creditor ob) 2)))))]
                 (nth (:debtor ob) 2)))
        ordinary (set (for [[e target _] (:fdeps (wr s dw)) :when (and (not= e :bundle) (= v target))] e))
        ended (set/difference (nth old 2 #{}) d ordinary)
        s (if old (update-in s [:worlds dw :fdeps] disj old) s)
        s (if (seq d) (update-in s [:worlds dw :fdeps] conj [:bundle v d]) s)]
    (if (seq ended) (cleanup-dependency s dw [:bundle v ended] v) s)))

(defn timer-prune
  "Resource bookkeeping may end before its borrowed ordinary slice returns.
   The ordinary thread remains independent physical evidence through T38."
  [s n]
  (let [{:keys [owner phase install handle frames] :as row} (get-in s [:env :native n])
        [w r] owner]
    (if (and (cleanup/timer-resource? row) (not= :armed phase) (not= :pending install)
             (empty? frames) (#{:none :released :failed} handle))
      (let [s (update-in s [:env :native] dissoc n)]
        (if (and (= :unwinding (:status (run s w r))) (not (physical? s w r)))
          (update-in s [:worlds w :runs] dissoc r) s)) s)))

(defn timer-revoke [s n]
  (let [row (get-in s [:env :native n])]
    (if (and (cleanup/timer-resource? row) (= :armed (:phase row)))
      (timer-prune
       (update-in s [:env :native n]
                  #(cond-> (-> % (assoc :phase :revoked) (dissoc :value))
                     (= :present (:handle %)) (assoc :handle :release-pending))) n) s)))

(declare queue-mailbox-rejection)

(defn end-obligation
  ([s w o cause] (end-obligation s w o cause nil))
  ([s w o cause cancellation]
   (if-let [ob (get-in s [:worlds w :obligations o])]
     (let [cancellation (or cancellation *release-cancellation*)
           [kind dw e] (:debtor ob)
           [ck cw r] (:creditor ob)
           s (if (and (= :cancel-delivered cause) (= :await-reactive (:kind ob))
                      (= :consumed (:slot ob)) (= :run ck)
                      (#{:running :parked :inherited :completed} (:status (run s cw r)))
                      (= r (current s cw (first r))))
               (cond-> (assoc-in s [:worlds cw :runs r :validation-lost?] true)
                 (:completed? (ent s cw (first r)))
                 (assoc-in [:worlds cw :entities (first r) :dirty?] true)) s)
           s (if (and (= :entity kind) (= :host ck) (= :cancel-delivered cause)
                      (cleanup/mailbox-control s dw e e))
               (queue-mailbox-rejection s dw e o (if cancellation (:value cancellation) :org.replikativ.spindel.engine.protocols/cancelled)) s)
           s (if (and (= :entity kind) (cleanup/mailbox-control s dw e e) (not= :delivered cause))
               (cleanup/detach-mailbox-consumer s dw e e [(if (= :host ck) :host :obligation) o]) s)
           s (if (:timer ob) (timer-revoke s (:timer ob)) s)
           s (-> s
                 (update-in [:worlds w :obligations] dissoc o)
                 (emit {:event :obligation-exit :world w :o o :ob ob :cause cause}))
           s (if (and (= cause :cancel-delivered) (= :host (first (:creditor ob)))
                      (not (cleanup/mailbox-control s dw e e))
                      (not (#{:claimed :entered}
                            (get-in (cleanup/mailbox-control s dw e e)
                                    [:reservations [:host o] :state]))))
               (emit s {:event :host-delivery :world w :o o
                        :value (if cancellation (:value cancellation) ::cancelled)}) s)
           s (if (and (= :entity kind) (not= dw w) (= :run (first (:creditor ob))) (not= :released (:status (wr s dw))))
               (let [fd [e w o]
                     s (if (contains? (:fdeps (wr s dw)) fd) (cleanup-dependency s dw fd w) s)]
                 (sync-bundle s dw w)) s)]
       (if (and (= :external (:kind ob)) (:token ob))
         (assoc-in s [:env :waiters (:token ob) :armed?] true) s)) s)))

(defn add-fdep [s w o]
  (let [ob (get-in s [:worlds w :obligations o]) [k dw e] (:debtor ob)]
    (if (and (= k :entity) (not= dw w) (= :run (first (:creditor ob)))
             (not= :released (:status (wr s dw)))
             (not (pending-start? s w o ob)) (not (cancelling? s w o ob)))
      (if (= :inherited (:status (run s w (nth (:creditor ob) 2))))
        (let [old (first (filter #(and (= :bundle (first %)) (= w (second %))) (:fdeps (wr s dw))))]
          (-> s (update-in [:worlds dw :fdeps] disj old)
              (update-in [:worlds dw :fdeps] conj [:bundle w (conj (nth old 2 #{}) e)])))
        (update-in s [:worlds dw :fdeps] (fnil conj #{}) [e w o])) s)))

(declare t06-resume t09-reenter t10-supersede t11-cancel t13-close-scope
         t26-seal t34-release-world rule-l t08-deliver t36-cleanup t25-cut-fail step)

(def ^:dynamic *fresh-runs* nil)

(defn allocate-generation [s w e dense]
  (if *fresh-runs*
    (let [[world entity stamp :as witness] (first @*fresh-runs*)]
      (require! (and (vector? witness) (= 3 (count witness))
                     (= w world) (= e entity) (integer? stamp)
                     (> stamp (reduce max 0 (vals (:generation-clock s)))))
                ::invalid-run-allocation {:expected [w e] :witness witness})
      (vswap! *fresh-runs* next)
      stamp)
    dense))

(defn start-run [s w e owner cause]
  (require! (not (#{:deferred :mailbox} (:kind (ent s w e)))) ::not-computation {:w w :e e})
  (let [inherited (for [[r rr] (:runs (wr s w))
                        :when (and (= e (:spin rr)) (= :inherited (:status rr)))] r)
        s (reduce #(t11-cancel %1 {:w w :r %2}) s (sort-by pr-str inherited))
        ;; An unwinding row is physical evidence, never a predecessor index.
        pred (let [r (current s w e)] (when (not= :unwinding (:status (run s w r))) r))
        n (allocate-generation s w e (inc (max (or (second pred) 0) (get-in s [:generation-clock [w e]] 0)))) r [e n]
        seqno (inc (max (get-in s [:worlds w :seq] 0) (get-in s [:clocks w] 0)))]
    (require! (= :live (:status (wr s w))) ::sealed {:world w})
    (require! (open? s w owner) ::closed-scope {:world w :scope owner})
    [(-> s (assoc-in [:generation-clock [w e]] n) (assoc-in [:worlds w :seq] seqno)
         (update-in [:worlds w :entities e] dissoc :cancelled-completion)
         (assoc-in [:worlds w :runs r]
                   {:spin e :owner owner :pred pred
                    :ancestors (cond-> (get-in s [:worlds w :runs pred :ancestors] #{}) pred (conj pred))
                    :status :running
                    :creations #{} :spawned #{} :seq seqno})
         (cond-> (run s w owner) (update-in [:worlds w :runs owner :spawned] conj r))
         (emit {:event :body-entry :world w :e e :r r :cause cause
                :completed? (:completed? (ent s w e)) :reasons (reasons s w e)
                :reachable? (boolean
                             (some (fn [[_ h]] (and (= e (:spin h)) (:reachable? h)
                                                    (contains? (:touched h) w)))
                                   (get-in s [:env :handles])))})) r]))

(def ^:dynamic *cascading?* false)

(defn signal-dependent?
  "A detached cache loses validation when it reaches a source or dirty cache.
  Search before retiring outgoing obligations; cycles alone are not mutable."
  [s w e]
  (loop [todo [[w e]] seen #{}]
    (if-let [[w e :as key] (peek todo)]
      (let [todo (pop todo) er (ent s w e)]
        (cond
          (contains? seen key) (recur todo seen)
          (or (#{:signal :atom} (:kind er)) (:dirty? er)) true
          :else
          (recur (into todo (for [[_ ob] (:obligations (wr s w))
                                  :let [[ck cw r] (:creditor ob)
                                        [dk dw de] (:debtor ob)]
                                  :when (and (= :run ck) (= w cw) (= e (:spin (run s w r)))
                                             (#{:track :await-reactive} (:kind ob)) (= :entity dk))]
                              [dw de]))
                 (conj seen key))))
      false)))

(defn idle-retirement-order
  "Actual mixed Run/Scope ownership precedence before any idle detach.
   Entity lifetime remains an owner-release effect, not a scheduling edge."
  [s w idle]
  (let [idle (set idle)
        selected (set (for [[r row] (:runs (wr s w))
                            :when (and (contains? idle (:spin row)) (#{:completed :stale} (:status row)))] r))
        dependencies (into {}
                           (for [r selected :let [execution (rest (butlast (owner-chain s w r)))]]
                             [r (set/intersection selected (set (filter #(run s w %) execution)))]))]
    (loop [remaining selected result []]
      (if (empty? remaining) result
          (let [ready (sort-by pr-str (filter #(empty? (set/intersection remaining (get dependencies %))) remaining))]
            (require! (seq ready) ::retirement-precedence-cycle
                      {:w w :runs remaining :dependencies (select-keys dependencies remaining)})
            (recur (apply disj remaining ready) (into result ready)))))))

(defn rule-l
  "§4.3 reclamation fixpoint, including idle completed-row normalization."
  [s w]
  (if (or *cascading?* (= :released (:status (wr s w)))) s
      (binding [*cascading?* true
                *liveness-cache* (or *liveness-cache* (volatile! nil))]
        (loop [s s]
          (let [world (wr s w)
                idle (for [[e er] (:entities world)
                           :when (and (= :spin (:kind er)) (:completed? er)
                                      (not *cache-gc-only?*)
                                      (not (execution-live? s w e)))] e)
                ;; Preserve all invalidation proofs while the complete BEFORE
                ;; graph is still available. Parent teardown may remove a child's
                ;; dependency rows and must not make a cache look independent.
                signal-dependent (filter #(signal-dependent? s w %) idle)
                retirement (idle-retirement-order s w idle)
                marked (reduce #(assoc-in %1 [:worlds w :entities %2 :dirty?] true) s signal-dependent)
                retired (reduce (fn [state r]
                                  (if (#{:completed :stale} (:status (run state w r)))
                                    (t10-supersede state {:w w :r r}) state)) marked retirement)
                normalized (reduce (fn [state e]
                                     (if (ent state w e) (assoc-in state [:worlds w :entities e :owner] nil) state))
                                   retired (sort-by pr-str idle))
                dead (for [[e er] (:entities (wr normalized w))
                           :when (and (empty? (reasons normalized w e))
                                      (not (and (idle? normalized w e) (seq (:tokens er)))))] e)]
            (if (and (empty? dead) (= s normalized)) (prune-ancestry normalized w)
                (recur
                 (reduce
                  (fn [s e]
                    (let [rs (for [[r rr] (:runs (wr s w)) :when (= e (:spin rr))] r)
                          s (reduce #(t11-cancel %1 {:w w :r %2}) s (sort-by pr-str rs))]
                      (-> s (update-in [:worlds w :entities] dissoc e)
                          (update-in [:worlds w :pins] disj e)
                          (update-in [:worlds w :queue]
                                     #(vec (remove (fn [ev] (or (and (= e (:completion ev)) (= w (:debtor-world ev)))
                                                                (= e (:signal-write ev)))) %)))
                          (update-in [:worlds w :runs]
                                     (fn [runs] (into {} (for [[r rr] runs]
                                                           [r (update rr :creations disj e)])))))))
                  normalized (sort-by pr-str dead)))))))))

(defn t01-create-spin
  "T1 create-spin: host handles, lexical creations and predecessor adoption."
  [s {:keys [e tok] :as a}]
  (let [w (selected s a) owner (cs s a w) old (ent s w e)
        r (run s w owner) adopt? (and r old (predecessor? s w (:creator old) owner))]
    (live! s w)
    (require! (not (#{:deferred :mailbox} (:kind old))) ::not-computation {:w w :e e})
    (when-let [h (get-in s [:env :handles tok])]
      (require! (= e (:spin h)) ::token-spin-mismatch {:tok tok :e e :handle h}))
    (let [s (if (or (nil? tok) (get-in s [:env :handles tok])) s
                (assoc-in s [:env :handles tok]
                          {:spin e :reachable? true :touched #{} :dropped #{}}))
          s (if (and r (or (nil? old) adopt?))
              (-> s (assoc-in [:worlds w :entities e]
                              (merge (or old (spin-row s w e owner))
                                     {:owner owner :creator owner :kept? (reactive? s w owner) :order (get a :order 0)}))
                  (update-in [:worlds w :runs owner :creations] conj e)) s)
          s (if adopt?
              (update-in s [:worlds w :runs]
                         #(into {} (for [[rid rr] %]
                                     [rid (if (and (= e (:spin rr)) (= (:creator old) (:owner rr)))
                                            (assoc rr :owner owner) rr)]))) s)]
      (touch s w e tok))))

(defn t02-create-signal
  "T2 create-signal/create-atom. Keyed lookup follows lineage ancestors."
  [s {:keys [e kind key value order] :or {kind :signal order 0} :as a}]
  (let [w (selected s a) owner (cs s a w) e (if key (keyid s w key) e)
        source (loop [v w]
                 (cond (ent s v e) v
                       (and key (get-in s [:worlds v :lineage :parent]))
                       (recur (get-in s [:worlds v :lineage :parent])) :else nil))]
    (live! s w)
    (require! (open? s w owner) ::closed-scope {:scope owner})
    (if source
      (let [er (ent s source e)]
        (require! (and (= :signal (:kind er)) (= key (:key er))) ::key-collision {:e e})
        (if (and (= source w) (predecessor? s w (:owner er) owner))
          (-> s (assoc-in [:worlds w :entities e :owner] owner)
              (assoc-in [:worlds w :entities e :order] order)
              (update-in [:worlds w :runs owner :creations] conj e)) s))
      (cond-> (assoc-in s [:worlds w :entities e]
                        (cond-> (assoc (row kind owner) :key key :result value :order order)
                          (contains? a :allocation) (assoc :allocation (:allocation a))))
        (run s w owner) (update-in [:worlds w :runs owner :creations] conj e)))))

(defn t03-touch-keyed
  "T3 touch-keyed/cache-row, indexed by spin instance."
  [s {:keys [w r key kind order] :or {kind :cache-row order 0}}]
  (require! (not (#{:deferred :mailbox} kind)) ::reserved-source-kind {:kind kind})
  (require! (work? (run s w r)) ::not-work {:r r})
  (let [e [(:spin (run s w r)) key]]
    (require! (not (#{:deferred :mailbox} (:kind (ent s w e)))) ::reserved-source-kind {:e e :kind :deferred})
    (-> s (assoc-in [:worlds w :entities e] (assoc (row kind r) :order order))
        (update-in [:worlds w :runs r :creations] conj e))))

(defn read-source [s w e]
  (loop [v w]
    (cond (ent s v e) v
          (and (= :following (get-in s [:worlds v :lineage :mode]))
               (get-in s [:worlds v :lineage :parent]))
          (recur (get-in s [:worlds v :lineage :parent]))
          :else nil)))
(defn executable! [s w]
  (live! s w)
  (require! (not-any? #(and (= w (:child %)) (= :attached (:phase %)))
                      (vals (:cuts s))) ::not-admitted {:w w}))

(defn invalidate-computation
  "Invalidate constructor captures without executing or retiring a generation."
  [s {:keys [w e]}]
  (executable! s w)
  (require! (= :open (:admission (wr s w))) ::not-admitted {:world w})
  (require! (= :spin (:kind (ent s w e))) ::not-computation {:w w :e e})
  (let [r (current s w e)]
    (cond-> (assoc-in s [:worlds w :entities e :dirty?] true)
      (run s w r) (assoc-in [:worlds w :runs r :validation-lost?] true))))

(defn publish-signal
  "Publish a source's committed value without writing it again."
  [s {:keys [w e]}]
  (executable! s w)
  (require! (= :open (:admission (wr s w))) ::not-admitted {:world w})
  (let [source (ent s w e)]
    (require! (and (#{:signal :atom} (:kind source)) (:owner source)) ::released {:w w :e e})
    (reduce #(enqueue %1 %2 {:completion e :debtor-world w :value (:result source) :source-change? true})
            s (conj (fdep-targets (wr s w) e) w))))

(defn deferred-create [s {:keys [w e allocation] :as action}]
  (executable! s w)
  (require! (= :open (:admission (wr s w))) ::not-admitted {:world w})
  (require! (= e allocation) ::allocation-mismatch {:w w :e e :allocation allocation})
  (require! (nil? (ent s w e)) ::released-deferred {:w w :e e})
  (let [s (t02-create-signal s (assoc action :kind :deferred :value nil))]
    (assoc-in s [:worlds w :entities e :deferred] {:claimed? false :protected {}})))

(defn- deferred-view [s {:keys [w e allocation cell]} fallback?]
  (require! (= e allocation) ::allocation-mismatch {:w w :e e :allocation allocation})
  (let [source (ent s w e)
        live? (and (= :deferred (:kind source)) (= allocation (:allocation source)) (:owner source))
        matches (when (and fallback? (nil? cell) (not live?))
                  (for [[key row] (get-in s [:env :cleanup-cells])
                        :when (and (= w (first key)) (= e (nth key 2))
                                   (= allocation (:allocation row)) (= :deferred (:kind row))
                                   (seq (:holders row)))] key))
        cell (or cell (first matches))
        retained (when cell (get-in s [:env :cleanup-cells cell]))]
    (cond
      (and cell (= w (first cell)) (= e (nth cell 2 nil))
           (= :deferred (:kind retained)) (= allocation (:allocation retained))
           (seq (:holders retained)))
      {:path [:env :cleanup-cells cell] :row retained :cell cell
       :assigned? (get-in retained [:deferred :assigned?])}
      cell nil
      live?
      {:path [:worlds w :entities e] :row source :assigned? (:completed? source)})))

(defn- admit-deferred-view! [s {:keys [w th cell op frame callback]} view]
  (when callback
    (let [receipt (get-in s [:env :native callback])]
      (require! (and (cleanup/mailbox-callback? receipt) (= w (first (:owner receipt)))
                     (= frame (:frame receipt))
                     (and (:cell view) (contains? (:cells receipt #{}) (:cell view))
                          (contains? (:holders (:row view) #{}) callback)))
                ::released-deferred {:callback callback :cell cell})))
  (when op
    (let [participant (cleanup/operation s op) ticket (get-in s [:env :native (first op)])]
      (require! (and participant (= w (first (:owner ticket)))
                     (contains? (:frames participant) frame)
                     (or (not (cleanup/exit? ticket)) (:cell view))
                     (or (nil? (:cell view))
                         (and (contains? (:cells ticket #{}) (:cell view))
                              (contains? (:holders (:row view) #{}) (first op)))))
                ::released-deferred {:w w :op op :cell cell})))
  (require! view ::released-deferred {:w w :cell cell})
  (let [thread (get-in s [:env :threads th]) r (:run thread)
        retired? (= :unwinding (:status (run s (:world thread) r)))]
    (if (:cell view)
      (when r
        (require! (and cell (= w (:world thread))
                       (contains? (:holders (:row view)) (or (:cleanup-ticket thread) (cleanup/ticket w r))))
                  ::released-deferred {:w w :cell cell :th th}))
      (do (require! (not retired?) ::cancelled {:w w :r r})
          (executable! s w)
          (require! (= :open (:admission (wr s w))) ::not-admitted {:world w})))))

(defn deferred-request [s {:keys [w e allocation value claim? cell] :as action}]
  (let [{:keys [path row] :as view} (deferred-view s action false)]
    (admit-deferred-view! s action view)
    (if (and claim? (get-in row [:deferred :claimed?])) s
        (let [s (if claim? (cleanup/update-deferred-resource s w e allocation #(assoc % :claimed? true)) s)
              event (cond-> {:deferred-assignment e :allocation allocation :value value}
                      cell (assoc :cell cell))]
          (if (= :released (:status (wr s w)))
            (let [n (inc (max (get-in s [:worlds w :seq] 0) (get-in s [:clocks w] 0)))]
              (-> s (assoc-in [:clocks w] n)
                  (update-in [:env :outside] conj {:w w :event (assoc event :seq n)})))
            (enqueue s w event))))))

(defn deferred-assign [s {:keys [w e allocation value seq cell] :as action}]
  (let [queued (first (:queue (wr s w)))
        outside (first (filter #(= w (:w %)) (get-in s [:env :outside])))
        front (or queued (:event outside))]
    (require! (= (select-keys front [:deferred-assignment :allocation :seq :cell])
                 (cond-> {:deferred-assignment e :allocation allocation :seq seq}
                   cell (assoc :cell cell)))
              ::not-deferred-assignment {:w w :e e :front front})
    (require! (or (not (contains? action :value)) (= value (:value front)))
              ::not-deferred-assignment {:w w :e e :front front})
    (let [value (:value front)
          s (if queued (update-in s [:worlds w :queue] #(vec (rest %)))
                (update-in s [:env :outside]
                           #(let [[a b] (split-with (fn [held] (not= held outside)) %)]
                              (into (vec a) (rest b)))))
          ;; The original cohort is authenticated above. Its holder may have
          ;; returned since acceptance; resolve only this same allocation.
          {:keys [path row assigned? cell] :as view}
          (or (deferred-view s action true)
              (deferred-view s (dissoc action :cell) true))]
      (if (or (nil? view) assigned?) s
          (let [protected (get-in row [:deferred :protected])
                s (cleanup/update-deferred-resource s w e allocation
                                                    #(assoc % :value value :assigned? true :protected {}))
                s (reduce (fn [s [reg edge]] (cleanup/operation-deliver s {:op (:operation edge) :reg reg :value value}))
                          s protected)]
            (if cell s
                (reduce #(enqueue %1 %2 {:completion e :debtor-world w :value value})
                        s (conj (fdep-targets (wr s w) e) w))))))))

(defn deferred-observe [s {:keys [w e host] :or {host :caller} :as action}]
  (let [{:keys [row assigned?] :as view} (deferred-view s action false)]
    (require! (and view (not (:cell view))) ::released-deferred {:w w :e e})
    (admit-deferred-view! s action view)
    (if assigned?
      (emit s {:event :host-delivery :world w :e e :value (:result row)})
      (let [[s o] (allocate s :o)]
        (assoc-in s [:worlds w :obligations o]
                  {:kind :deref :debtor [:entity w e] :creditor [:host host]
                   :standing? false :cont nil :token nil :order 0 :slot :armed
                   :filter {:mode :local :origin w}})))))

(defn operation-await-deferred [s {:keys [w op n sequence reg frame allocation e] :as action}]
  (let [operation (cleanup/operation-frame! s action)
        ticket (get-in s [:env :native n])
        {:keys [row assigned?] :as view}
        (deferred-view s (if (get-in s [:env :cleanup-cells (:cell action)])
                           action (dissoc action :cell)) false)
        key (or (:cell view) [w (:owner row) e])]
    (require! (and view (= w (first (:owner ticket)))
                   (or (nil? (:cell action)) (= key (:cell action)))
                   (= reg [op (inc (:next-registration operation))]))
              ::not-operation-registration {:op op :reg reg})
    (if (:cell view)
      (require! (and (contains? (:cells ticket #{}) key)
                     (contains? (:holders row #{}) n)) ::released-deferred {:cell key})
      (do (executable! s w)
          (require! (= :open (:admission (wr s w))) ::not-admitted {:world w})))
    (let [s (-> s
                (update-in [:env :cleanup-cells key]
                           (fn [old]
                             (assoc (or old {:kind :deferred :allocation allocation :result (:result row)
                                             :deferred (assoc (:deferred row) :assigned? (boolean assigned?))})
                                    :holders (conj (:holders old #{}) n))))
                (update-in [:env :native n :cells] (fnil conj #{}) key)
                (update-in [:env :native n :operation :next-registration] inc)
                (assoc-in [:env :native n :operation :registrations reg]
                          (cond-> {:w w :e e :allocation allocation :cell key
                                   :state (if assigned? :claimed :pending) :continuation reg :entered? false}
                            assigned? (assoc :delivery (:result row)))))]
      (if assigned? s
          (cleanup/update-deferred-resource s w e allocation
                                            #(assoc-in % [:protected reg] {:operation op :sequence sequence}))))))

(declare finish-unwinding)

(def mailbox-empty {:messages [] :consumers [] :pending {} :reservations {} :protected {} :physical {}})

(defn mailbox-create [s {:keys [w e allocation] :as action}]
  (executable! s w)
  (require! (= :open (:admission (wr s w))) ::not-admitted {:world w})
  (require! (= e allocation) ::allocation-mismatch {:w w :e e :allocation allocation})
  (require! (nil? (ent s w e)) ::released-mailbox {:w w :e e})
  (assoc-in (t02-create-signal s (assoc action :kind :mailbox :value nil))
            [:worlds w :entities e :mailbox] mailbox-empty))

(defn mailbox-view [s {:keys [w e allocation cell]} fallback?]
  (require! (= e allocation) ::allocation-mismatch {:w w :e e :allocation allocation})
  (let [source (ent s w e)
        live? (and (= :mailbox (:kind source)) (= allocation (:allocation source)) (:owner source))
        cell (or cell (when (and fallback? (not live?))
                        (first (for [[key row] (get-in s [:env :cleanup-cells])
                                     :when (and (= w (first key)) (= e (nth key 2 nil))
                                                (= :mailbox (:kind row)) (= allocation (:allocation row))
                                                (seq (:holders row)))] key))))
        retained (get-in s [:env :cleanup-cells cell])]
    (cond
      (and cell (= w (first cell)) (= e (nth cell 2 nil)) (= :mailbox (:kind retained))
           (= allocation (:allocation retained)) (seq (:holders retained)))
      {:row retained :cell cell :control (:mailbox retained)}
      cell nil
      live? {:row source :control (:mailbox source)})))

(defn- admit-mailbox! [s {:keys [w th op frame callback] :as action} view]
  (require! view ::released-mailbox {:w w :e (:e action) :cell (:cell action)})
  (let [thread (get-in s [:env :threads th])
        ticket (get-in s [:env :native (when op (first op))])
        participant (cleanup/operation s op)
        raw (get-in s [:env :native callback])
        held? (fn [receipt id]
                (and (:cell view) (contains? (:cells receipt #{}) (:cell view))
                     (contains? (:holders (:row view) #{}) id)))]
    (cond
      op (require! (and participant (= w (first (:owner ticket)))
                        (contains? (:frames participant) frame)
                        (if (:cell view) (held? ticket (first op)) (not (cleanup/exit? ticket))))
                   ::released-mailbox {:op op :frame frame})
      callback (require! (and (cleanup/mailbox-callback? raw) (= frame (:frame raw))
                              (= w (first (:owner raw)))
                              (if (:cell view) (held? raw callback)
                                  (and (not (:retired? raw))
                                       (= :mailbox (:kind (:row view)))
                                       (= (:allocation action) (:allocation (:row view)))
                                       (:owner (:row view)))))
                         ::released-mailbox {:callback callback :frame frame})
      (:cleanup-ticket thread)
      (let [id (:cleanup-ticket thread) receipt (get-in s [:env :native id])]
        (require! (and (= w (:world thread)) (= :claimed (:phase receipt)) (held? receipt id))
                  ::released-mailbox {:th th :cell (:cell view)}))
      (:run thread) (require! (and (= w (:world thread)) (not (:retired? thread))
                                   (not= :unwinding (:status (run s w (:run thread))))
                                   (nil? (:cell view))) ::cancelled {:w w :th th})
      (:cell view) (require! (= :mailbox-post-request (:t action)) ::released-mailbox {:cell (:cell view)})
      :else nil)
    (when-not (:cell view)
      (executable! s w)
      (require! (= :open (:admission (wr s w))) ::not-admitted {:world w}))))

(defn mailbox-post-request [s {:keys [w e allocation value message-id] :as action}]
  (let [view (mailbox-view s action true)
        sequence (inc (max (get-in s [:worlds w :seq] 0) (get-in s [:clocks w] 0)))
        id [allocation sequence]]
    (admit-mailbox! s action view)
    (require! (or (nil? message-id) (= id message-id)) ::mailbox-message-mismatch {:message-id message-id})
    (cleanup/mailbox-envelope s w e allocation {:id id :value value} (:cell view) false)))

(defn mailbox-post [s {:keys [w e allocation seq message-id cell] :as action}]
  (let [queued (first (:queue (wr s w)))
        outside (first (filter #(= w (:w %)) (get-in s [:env :outside])))
        front (or queued (:event outside))
        fields [:mailbox-post :allocation :seq :message-id :cell]]
    (require! (= (select-keys front fields)
                 (select-keys (assoc action :mailbox-post e) fields))
              ::not-mailbox-post {:w w :e e :front front})
    (let [view (or (mailbox-view s action true) (mailbox-view s (dissoc action :cell) true))
          _ (require! (or (not (contains? action :consumer))
                          (= (:consumer action) (first (get-in view [:control :consumers]))))
                      ::not-mailbox-post {:consumer (:consumer action)})
          s (if queued (update-in s [:worlds w :queue] #(vec (rest %)))
                (update-in s [:env :outside]
                           #(let [[a b] (split-with (fn [held] (not= held outside)) %)]
                              (into (vec a) (rest b)))))
          control (:control view) consumer (first (:consumers control))
          pending (get-in control [:pending consumer])
          message {:id (:message-id front) :value (:value front)}]
      (if-not view s
              (let [s (cleanup/update-mailbox-resource
                       s w e allocation
                       (fn [control]
                         (if-not consumer (update control :messages conj message)
                                 (-> control (update :consumers #(vec (rest %)))
                                     (update :pending dissoc consumer)
                                     (assoc-in [:reservations consumer]
                                               (merge pending {:message-id (:id message) :value (:value message) :state :reserved}))
                                     (cond-> (= :operation (:kind pending)) (update :protected dissoc (:reg pending)))))))
                    s (case (:kind pending)
                        :ordinary (assoc-in s [:worlds w :runs (:r pending) :status] :running)
                        :operation (update-in s [:env :native (first (:op pending)) :operation :registrations (:reg pending)]
                                              assoc :state :ready :delivery (:value message) :message-id (:id message))
                        s)]
                (emit s {:event :mailbox-post :world w :e e :message-id (:id message)
                         :consumer consumer :value (:value message)}))))))

(defn queue-mailbox-rejection [s w e o reason]
  (let [consumer [:host o] control (cleanup/mailbox-control s w e e)
        target (or (get-in control [:pending consumer]) (get-in control [:reservations consumer]))
        reservation (get-in control [:reservations consumer])
        source (ent s w e)
        key (or (when (:owner source) [w (:owner source) e])
                (first (for [[key row] (get-in s [:env :cleanup-cells])
                             :when (and (= w (first key)) (= e (nth key 2 nil)) (= :mailbox (:kind row)))] key)))
        owner (second key) receipt [:mailbox-callback w owner consumer]]
    (if (or (nil? target) (#{:claimed :entered} (:state reservation))
            (get-in s [:env :native receipt])) s
        (let [s (cleanup/detach-mailbox-consumer s w e e consumer)
              control (cleanup/mailbox-control s w e e)
              row {:kind :mailbox-callback :owner [w owner] :anchor (owner-chain s w owner)
                   :state :running :cells #{key} :consumer consumer :consumer-kind :host :allocation e
                   :frame nil :retired? true :phase :queued :physical? false
                   :variant :error :delivery reason}]
          (-> s (assoc-in [:env :native receipt] row)
              (update-in [:env :cleanup-cells key]
                         #(assoc (or % {:kind :mailbox :allocation e :result nil :mailbox control})
                                 :holders (conj (:holders % #{}) receipt))))))))

(defn seat-mailbox-physical [s w e allocation consumer kind frame view]
  (let [source (ent s w e)
        live? (and (= :mailbox (:kind source)) (= allocation (:allocation source)) (:owner source))
        owner (if live? (:owner source) (second (:cell view)))
        key (if live? [w owner e] (:cell view)) anchor (owner-chain s w owner)
        receipt [:mailbox-callback w owner consumer] control (:control view)
        row {:kind :mailbox-callback :owner [w owner] :anchor anchor :state :running
             :cells #{key} :consumer consumer :consumer-kind kind :allocation allocation :frame frame :retired? false
             :phase :executing :physical? true :variant :ok}]
    (-> s (assoc-in [:env :native receipt] row)
        (update-in [:env :cleanup-cells key]
                   #(assoc (or % {:kind :mailbox :allocation allocation :result nil :mailbox control})
                           :holders (conj (:holders % #{}) receipt)))
        (cleanup/update-mailbox-resource w e allocation
                                         #(assoc-in % [:physical frame] {:consumer consumer :owner [w owner]
                                                                         :anchor anchor :kind kind})))))

(defn mailbox-take [s {:keys [w e allocation consumer kind o r order host available? th] :or {order 0 host :caller} :as action}]
  (let [view (mailbox-view s action false) control (:control view)
        message (first (:messages control))
        expected-o (fresh s :o)
        expected-consumer [(if (= :ordinary kind) :obligation :host) expected-o]]
    (admit-mailbox! s action view)
    (require! (not (and (:callback action)
                        (or (get-in s [:env :native (:callback action) :retired?])
                            (not (:owner (ent s w e))))))
              ::cleanup-only {:action action})
    (require! (and (or (nil? (:callback action)) (= :host kind))
                   (#{:ordinary :host} kind) (= o expected-o) (= consumer expected-consumer)
                   (or (not (contains? action :available?)) (= available? (boolean message))))
              ::not-mailbox-consumer {:consumer consumer :o o :kind kind})
    (when (= :ordinary kind)
      (require! (and (= :running (:status (run s w r))) (= r (current s w (first r))))
                ::not-running {:w w :r r})
      (when message
        (let [thread (get-in s [:env :threads th])]
          (require! (and (:executing? thread) (= [w r] [(:world thread) (:run thread)]))
                    ::not-mailbox-frame {:th th :r r}))))
    (let [[s _] (allocate s :o)
          pending (cond-> {:kind kind :o o :order order} (= :ordinary kind) (assoc :r r))
          ob (if (= :ordinary kind)
               {:kind :await-once :debtor [:entity w e] :creditor [:run w r] :standing? false
                :cont [:continuation o] :token nil :order order :origin :created :slot :armed}
               {:kind :deref :debtor [:entity w e] :creditor [:host host] :standing? false
                :cont nil :token nil :order 0 :slot :armed :filter {:mode :local :origin w}})
          s (assoc-in s [:worlds w :obligations o] ob)
          s (if (and (= :ordinary kind) (not message)) (assoc-in s [:worlds w :runs r :status] :parked) s)]
      (let [s (cleanup/update-mailbox-resource
               s w e allocation
               (fn [control]
                 (if message
                   (-> control (update :messages #(vec (rest %)))
                       (assoc-in [:reservations consumer]
                                 (merge pending {:message-id (:id message) :value (:value message) :state :claimed
                                                 :frame [:mailbox-frame consumer]})))
                   (-> control (update :consumers conj consumer) (assoc-in [:pending consumer] pending)))))]
        (if message
          (seat-mailbox-physical s w e allocation consumer kind [:mailbox-frame consumer]
                                 (mailbox-view s action false)) s)))))

(defn mailbox-take-now [s {:keys [w e allocation available? r consumer-id] :as action}]
  (let [view (mailbox-view s action false)
        cancelled? (or (and r (not (#{:running :parked} (:status (run s w r)))))
                       (and consumer-id (or (:cancelled-completion (ent s w consumer-id))
                                            (= :unwinding (:status (run s w (current s w consumer-id)))))))
        message (when-not cancelled? (first (get-in view [:control :messages])))]
    (admit-mailbox! s action view)
    (require! (or (not (contains? action :available?)) (= available? (boolean message)))
              ::mailbox-availability-mismatch {:available? available?})
    (require! (or (not (contains? action :message-id))
                  (and message (= (:message-id action) (:id message))))
              ::mailbox-message-mismatch {:message-id (:message-id action)})
    (if message
      (-> (cleanup/update-mailbox-resource s w e allocation #(update % :messages (fn [xs] (vec (rest xs)))))
          (emit {:event :mailbox-immediate :world w :e e :message-id (:id message) :value (:value message)})) s)))

(defn mailbox-success-claim [s {:keys [w e allocation consumer message-id frame th inline?] :as action}]
  (let [view (mailbox-view s action true) control (:control view)
        reservation (get-in control [:reservations consumer])
        {:keys [kind o r]} reservation ob (get-in s [:worlds w :obligations o])
        physical (get-in control [:physical frame])
        owner (if physical (second (:owner physical)) (or (:owner (:row view)) (second (:cell view))))
        receipt [:mailbox-callback w owner consumer]
        thread (get-in s [:env :threads th]) ordinary? (= :ordinary kind)]
    (require! (and view (#{:ordinary :host} kind) (= message-id (:message-id reservation))
                   (= frame [:mailbox-frame consumer])
                   (if inline?
                     (and (= :claimed (:state reservation)) (= frame (:frame reservation))
                          (get-in s [:env :native receipt])
                          (or (not ordinary?)
                              (and (:executing? thread) (= [w r] [(:world thread) (:run thread)]))))
                     (and (= :reserved (:state reservation)) ob (= :armed (:slot ob))
                          (nil? (get-in s [:env :native receipt]))
                          (if ordinary?
                            (and (= [:run w r] (:creditor ob)) (= :running (:status (run s w r)))
                                 (= r (current s w (first r)))
                                 (nil? (:run thread)) (not (cleanup/active-slice? s w r)))
                            (= :host (first (:creditor ob)))))))
              ::not-mailbox-reservation {:consumer consumer :frame frame})
    (let [s (if inline? s (seat-mailbox-physical s w e allocation consumer kind frame view))
          s (-> s (cleanup/update-mailbox-resource w e allocation
                                                   #(-> % (assoc-in [:reservations consumer :state] :entered)
                                                        (assoc-in [:reservations consumer :frame] frame)))
                (end-obligation w o :delivered))
          s (if (and ordinary? (not inline?))
              (assoc-in s [:env :threads th]
                        (merge thread {:world w :scope r :run r :obligation-world w :executing? true})) s)
          s (if (and ordinary? (get-in s [:model :cps-exit?]) (not inline?))
              (assoc-in s [:worlds w :runs r :cps-entered?] true) s)]
      (emit s {:event :mailbox-entry :world w :e e :consumer consumer :message-id message-id
               :variant :ok :value (:value reservation)}))))

(defn mailbox-claim [s {:keys [w e allocation consumer frame callback variant] :as action}]
  (require! (or (nil? variant) (#{:ok :error} variant)) ::invalid-mailbox-variant {:variant variant})
  (if (= :error variant)
    (let [row (get-in s [:env :native callback]) control (cleanup/mailbox-control s w e allocation)]
      (require! (and (= e allocation (:allocation row)) (cleanup/mailbox-callback? row)
                     (= :queued (:phase row)) (false? (:physical? row)) (= :error (:variant row))
                     (not (contains? action :message-id))
                     (= consumer (:consumer row)) (= frame [:mailbox-frame consumer]) (nil? (:frame row))
                     (= w (first (:owner row))) control)
                ::not-mailbox-reservation {:consumer consumer :frame frame})
      (-> s (update-in [:env :native callback] assoc :phase :executing :physical? true :frame frame)
          (cleanup/update-mailbox-resource w e allocation
                                           #(assoc-in % [:physical frame] {:consumer consumer :owner (:owner row)
                                                                           :anchor (:anchor row) :kind :host}))
          (emit {:event :mailbox-rejection-entry :world w :e e :consumer consumer :variant :error :value (:delivery row)})))
    (mailbox-success-claim s action)))

(defn mailbox-return [s {:keys [w e allocation consumer frame]}]
  (let [control (cleanup/mailbox-control s w e allocation)
        physical (get-in control [:physical frame])
        owner (second (:owner physical)) receipt [:mailbox-callback w owner consumer]
        row (get-in s [:env :native receipt])]
    (require! (and (= allocation (:allocation row)) (= :executing (:phase row)) (:physical? row)
                   (= consumer (:consumer row)) (= frame (:frame row))
                   (= consumer (:consumer physical))
                   (or (= :error (:variant row))
                       (= :entered (get-in control [:reservations consumer :state])))) ::not-mailbox-frame {:consumer consumer :frame frame})
    (let [s (-> s (cleanup/update-mailbox-resource w e allocation
                                                   #(-> % (update :physical dissoc frame)
                                                        (update :reservations dissoc consumer)))
                (cleanup/release-cells receipt)
                (update-in [:env :native] dissoc receipt))]
      (if (run s w owner) (finish-unwinding s w owner) s))))

(defn mailbox-detach [s {:keys [w e allocation consumer]}]
  (let [control (cleanup/mailbox-control s w e allocation)
        pending (get-in control [:pending consumer]) reservation (get-in control [:reservations consumer])
        target (or pending reservation)]
    (require! (and control (or pending (= :reserved (:state reservation))))
              ::not-mailbox-consumer {:consumer consumer})
    (if-let [o (:o target)] (end-obligation s w o :creditor-cancelled)
            (require! false ::not-mailbox-consumer {:consumer consumer}))))

(defn operation-await-mailbox [s {:keys [w e allocation op n sequence reg frame] :as action}]
  (let [operation (cleanup/operation-frame! s action) ticket (get-in s [:env :native n])
        view (mailbox-view s (if (get-in s [:env :cleanup-cells (:cell action)]) action (dissoc action :cell)) false)
        row (:row view) control (:control view) key (or (:cell view) [w (:owner row) e])
        message (first (:messages control)) consumer [:operation reg]]
    (require! (and view (= w (first (:owner ticket))) (= reg [op (inc (:next-registration operation))])
                   (or (nil? (:cell action)) (= key (:cell action))))
              ::not-operation-registration {:op op :reg reg})
    (if (:cell view)
      (require! (and (contains? (:cells ticket #{}) key) (contains? (:holders row #{}) n))
                ::released-mailbox {:cell key})
      (do (executable! s w) (require! (= :open (:admission (wr s w))) ::not-admitted {:world w})))
    (let [pending {:kind :operation :op op :reg reg :order (second reg)}
          s (-> s
                (update-in [:env :cleanup-cells key]
                           #(assoc (or % {:kind :mailbox :allocation allocation :result nil :mailbox control})
                                   :holders (conj (:holders % #{}) n)))
                (update-in [:env :native n :cells] (fnil conj #{}) key)
                (update-in [:env :native n :operation :next-registration] inc)
                (assoc-in [:env :native n :operation :registrations reg]
                          (cond-> {:w w :e e :allocation allocation :cell key :continuation reg :entered? false
                                   :state (if message :claimed :pending)}
                            message (assoc :delivery (:value message) :message-id (:id message)))))]
      (cleanup/update-mailbox-resource
       s w e allocation
       (fn [control]
         (if message
           (-> control (update :messages #(vec (rest %)))
               (assoc-in [:reservations consumer]
                         (merge pending {:message-id (:id message) :value (:value message) :state :claimed :frame frame})))
           (-> control (update :consumers conj consumer) (assoc-in [:pending consumer] pending)
               (assoc-in [:protected reg] {:operation op :sequence sequence}))))))))

(defn operation-await [s action]
  (let [kind (or (:kind (ent s (:w action) (:e action)))
                 (get-in s [:env :cleanup-cells (:cell action) :kind]))]
    (if (= :mailbox kind) (operation-await-mailbox s action) (operation-await-deferred s action))))

(defn operation-deliver [_s action]
  (refuse ::unsupported-operation-delivery {:action action}))

(defn deferred-protect [_s action]
  (refuse ::obsolete-deferred-protection {:action action}))

(defn withdraw-deref
  "Withdraw one local host deref observer without cancelling its computation."
  [s {:keys [w o]}]
  (if-let [ob (get-in s [:worlds w :obligations o])]
    (do
      (require! (= :open (:admission (wr s w))) ::not-admitted {:world w})
      (require! (and (= :deref (:kind ob)) (not (:standing? ob))
                     (= :host (first (:creditor ob)))
                     (= :entity (first (:debtor ob))) (= w (second (:debtor ob))))
                ::not-host-deref {:w w :o o})
      (end-obligation s w o :creditor-cancelled))
    s))

(defn adopt-call-target
  "A successor that invokes/awaits a predecessor-owned spin adopts its
  ownership and its runs. Host-created handles have no lexical T1 to repeat."
  [s w e scope]
  (let [er (ent s w e) old (:owner er)]
    (if (and (= :spin (:kind er)) (predecessor? s w old scope))
      (-> s
          (assoc-in [:worlds w :entities e :owner] scope)
          (cond-> (= old (:creator er))
            (assoc-in [:worlds w :entities e :creator] scope)
            (= old (:creator er)) (assoc-in [:worlds w :entities e :kept?] (reactive? s w scope))
            (= old (:creator er)) (update-in [:worlds w :runs scope :creations] conj e))
          (update-in [:worlds w :runs]
                     #(into {} (for [[r rr] %]
                                 [r (if (and (= e (:spin rr)) (= old (:owner rr)))
                                      (assoc rr :owner scope) rr)]))))
      s)))
(defn t04-invoke
  "T4 invoke: join, cached delivery, or fresh body entry."
  [s {:keys [e tok mode host] :or {mode :deref host :caller} :as a}]
  (let [w (selected s a) owner (cs s a w)]
    (executable! s w)
    (require! (or (nil? tok) (get-in s [:env :handles tok])) ::unknown-handle {:tok tok})
    (require! (not (contains? (get-in s [:env :handles tok :dropped] #{}) w))
              ::idle-cache-released {:w w :e e :tok tok})
    (require! (open? s w owner) ::closed-scope {:scope owner})
    (let [source (read-source s w e)
          _ (require! (not (#{:deferred :mailbox} (:kind (ent s source e)))) ::not-computation {:w w :e e})
          foreign? (and source (not= source w))
          join? (and foreign? (or (work? (run s source (current s source e)))
                                  (:completed? (ent s source e))))
          dw (if join? source w)
          s (if (or (ent s w e) join?) s
                (assoc-in s [:worlds w :entities e]
                          (if foreign? (assoc (ent s source e) :owner (:root (wr s w))
                                              :tokens (covering-tokens s w e)
                                              :origin :copied :source-world source)
                              (spin-row s w e owner))))
          s (if join? s (adopt-call-target s w e owner))
          s (if (and (not join?) (nil? (:owner (ent s w e))))
              (assoc-in s [:worlds w :entities e :owner] owner) s)
          s (if join? s (touch s dw e tok))
          work (some (fn [[r rr]] (when (and (= e (:spin rr)) (work? rr)) r))
                     (:runs (wr s dw)))
          cached? (and (not work) (:completed? (ent s dw e)) (or (and foreign? join?) (not (:dirty? (ent s dw e)))))
          s (if (or work cached?) s (first (start-run s w e owner (if (:dirty? (ent s w e)) :dirty :invoke))))
          s (update-in s [:uses [:host-register dw e]] (fnil inc 0))
          [s o] (allocate s :o)
          ob {:kind mode :debtor [:entity dw e] :creditor [:host host]
              :standing? (= mode :callback) :cont nil :token nil :order 0
              :slot :armed :filter (get a :filter (get a :delivery-filter {:mode :local :origin w}))}]
      (if join?
        (enqueue s dw {:register-host o :ob ob :tok tok :e e :caller-world w})
        (cond-> s
          cached? (emit {:event :host-delivery :world w :e e :o o})
          (or (not cached?) (and (= mode :callback) (not (final? s dw e))))
          (assoc-in [:worlds dw :obligations o] ob))))))

(defn t05-park
  "T5 park on one of the five run-creditor obligation kinds."
  [s {:keys [w r kind debtor tok order recovery] :or {order 0 recovery :retry} :as a}]
  (live! s w)
  (require! (= :running (:status (run s w r))) ::not-running {:w w :r r})
  (require! (or (nil? tok) (get-in s [:env :handles tok])) ::unknown-handle {:tok tok})
  (require! (not (contains? (get-in s [:env :handles tok :dropped] #{}) w))
            ::idle-cache-released {:w w :tok tok})
  (let [[dk dw e] debtor
        _ (when (and (= :entity dk) (= :mailbox (:kind (ent s dw e))))
            (require! false ::unsupported-mailbox-obligation {:debtor debtor :kind kind}))
        _ (when (and (= :entity dk) (= :deferred (:kind (ent s dw e))))
            (require! (= :await-once kind) ::unsupported-deferred-obligation
                      {:w w :debtor debtor :kind kind}))
        await? (and (= :entity dk) (#{:await-once :await-reactive} kind)
                    (or (nil? (ent s dw e)) (= :spin (:kind (ent s dw e)))))
        foreign-cold? (and await? (not= dw w)
                           (not (work? (run s dw (current s dw e))))
                           (not (:completed? (ent s dw e))))
        s (if (and await? (= dw w) (nil? (ent s dw e)))
            (do (live! s dw) (assoc-in s [:worlds dw :entities e] (spin-row s dw e r))) s)
        s (if (and await? (= dw w)) (adopt-call-target s w e r) s)
        s (if (and await? (= dw w) (nil? (:owner (ent s dw e))))
            (assoc-in s [:worlds dw :entities e :owner] r) s)
        _ (when (and (= :entity dk) (not foreign-cold?))
            (require! (ent s dw e) ::missing-debtor {:debtor debtor}))
        completed? (and (= dk :entity) (:completed? (ent s dw e))
                        (or (not= dw w)
                            (and (not (:dirty? (ent s dw e)))
                                 (not (work? (run s dw (current s dw e)))))))
        s (update-in s [:uses [:register w r kind debtor]] (fnil inc 0))
        inline? (and (= kind :await-once) completed?)
        s (if (and await? (= dw w) (not completed?)
                   (not (work? (run s dw (current s dw e)))))
            (first (start-run s dw e r (if (:dirty? (ent s dw e)) :dirty :await))) s)]
    (if inline? (emit s {:event :inline-resume :world w :r r})
        (let [[s o] (allocate s :o) token [:cancel o]
              ob {:kind kind :debtor debtor :creditor [:run w r]
                  :standing? (boolean (standing kind)) :cont [:continuation o]
                  :token (when (= :external kind) token) :order order
                  :origin :created :slot (if (= kind :track) :consumed :armed)}
              s (-> s (assoc-in [:worlds w :runs r :status] (if (= kind :track) :running :parked))
                    (assoc-in [:worlds w :obligations o] ob))
              s (if foreign-cold?
                  (enqueue s dw {:start-for e :creditor-world w :o o :tok tok})
                  (add-fdep s w o))]
          (case kind
            :timer (assoc-in s [:worlds w :entities [:timer o]] (row :timer r))
            :external (-> s (assoc-in [:env :waiters token]
                                      {:world w :o o :registered? true :armed? false})
                          (assoc-in [:env :native token] {:owner [w r] :state :running
                                                          :recovery recovery}))
            (if foreign-cold? s (touch s dw e tok)))))))

(defn t06-resume
  "T6 consumes an armed slot; inherited activation requires live admitted world."
  [s {:keys [w o value] :or {value :value}}]
  (if-let [ob (get-in s [:worlds w :obligations o])]
    (let [[ck _ r] (:creditor ob) rr (run s w r)]
      (if (and (= :armed (:slot ob)) (= ck :run)
               (#{:parked :inherited} (:status rr)))
        (do
          (when (= :inherited (:status rr)) (executable! s w))
          (let [s (if (:standing? ob)
                    (assoc-in s [:worlds w :obligations o :slot] :consumed)
                    (end-obligation s w o :delivered))
                s (assoc-in s [:worlds w :runs r :status] :running)
                rows (filter (fn [[_ other]] (= [:run w r] (:creditor other))) (:obligations (wr s w)))
                s (reduce (fn [state [id _]] (add-fdep state w id)) s rows)
                debtors (set (for [[_ other] rows :let [[_ dw _] (:debtor other)] :when (and dw (not= dw w))] dw))
                s (reduce #(sync-bundle %1 %2 w) s debtors)
                s (reduce (fn [state [id other]]
                            (let [token [:cancel w id]]
                              (cond-> state
                                (:dormant? other) (assoc-in [:worlds w :obligations id :dormant?] false)
                                (= :timer (:kind other)) (assoc-in [:worlds w :obligations id :timer-armed?] true)
                                (= :external (:kind other)) (assoc-in [:worlds w :obligations id :token] token)
                                (= :external (:kind other)) (assoc-in [:env :waiters token] {:world w :o id :registered? true :armed? false})
                                (= :external (:kind other)) (assoc-in [:env :native token] {:owner [w r] :state :running :recovery :retry}))))
                          s rows)]
            (emit s {:event :resume :world w :r r :o o :one-shot? (not (:standing? ob))
                     :thread-world w :value value}))) s)) s))

(defn timer-register [s {:keys [w r o n th order delay-ms value] :or {order 0} :as action}]
  (let [thread (get-in s [:env :threads th]) rr (run s w r) expected (fresh s :o)]
    (live! s w)
    (require! (and (= :open (:admission (wr s w))) (= :running (:status rr))
                   (= r (current s w (:spin rr))) (= [w r] [(:world thread) (:run thread)])
                   (:executing? thread) (nil? (:cleanup-ticket thread))
                   (not (cleanup/protected? (get-in s [:env :native (cleanup/ticket w r)])))
                   (nil? (:op action)) (nil? (:callback action)))
              ::not-timer-activation {:action action})
    (require! (and (= o expected) (= n [:timer w o]) (number? delay-ms)
                   (nil? (get-in s [:env :native n]))) ::not-timer-registration {:action action})
    (let [[s _] (allocate s :o)
          ob {:kind :timer :debtor [:host :executor] :creditor [:run w r]
              :standing? false :cont [:continuation o] :token nil :order order
              :origin :created :slot :armed :timer n}
          row {:kind :timer-resource :owner [w r] :state :running :o o :order order
               :delay-ms delay-ms :value value :phase :armed :install :pending :handle :none
               :frames #{} :installer th :retired? false :anchor (owner-chain s w r)}]
      (-> s (assoc-in [:worlds w :obligations o] ob)
          (assoc-in [:worlds w :runs r :status] :parked)
          (assoc-in [:env :native n] row)))))

(defn- timer-settle [s n variant value]
  (let [{:keys [owner o] :as row} (get-in s [:env :native n]) [w r] owner
        s (update-in s [:env :native n]
                     #(cond-> (-> % (assoc :phase (if (= :ok variant) :fired :failed)) (dissoc :value))
                        (= :present (:handle %)) (assoc :handle :release-pending)))]
    (t06-resume s {:w w :o o :value value})))

(defn timer-install-result [s {:keys [w n variant handle? value] :as action}]
  (let [row (get-in s [:env :native n])
        installer (get-in s [:env :threads (:installer row)])]
    (require! (and (cleanup/timer-resource? row) (= w (first (:owner row)))
                   (= :pending (:install row)) (= (:owner row) [(:world installer) (:run installer)])
                   (:executing? installer) (#{:ok :error} variant)
                   (or (true? handle?) (false? handle?))
                   (or (= :ok variant) (false? handle?)))
              ::not-timer-install {:action action})
    (let [armed? (= :armed (:phase row))
          s (update-in s [:env :native n] assoc
                       :install (if (= :error variant) :failed (if handle? :seated :none))
                       :handle (if handle? (if armed? :present :release-pending) :none))
          s (if (= :error variant)
              (if armed? (timer-settle s n :error value)
                  (emit s {:event :timer-fault :world w :n n :stage :install :value value})) s)]
      (timer-prune s n))))

(defn timer-fire [s {:keys [w n frame variant value] :as action}]
  (let [{:keys [owner o phase] :as row} (get-in s [:env :native n]) [_ r] owner
        ob (get-in s [:worlds w :obligations o])]
    (require! (and (#{:ok :error} variant) (= frame [:timer-frame n 0]))
              ::not-timer-fire {:action action})
    ;; Cap-free late platform wrappers may call this gate; they acquire nothing.
    (if-not (and (cleanup/timer-resource? row) (= w (first owner)) (= :armed phase)
                 (= :live (:status (wr s w))) (= :open (:admission (wr s w)))
                 (= :parked (:status (run s w r))) (= r (current s w (first r)))
                 (= n (:timer ob)) (= :armed (:slot ob))) s
            (do
              (require! (or (= :error variant) (= value (:value row)))
                        ::not-timer-value {:action action})
              (let [s (assoc-in s [:env :native n :frames] #{frame})]
                (-> s (timer-settle n variant value)
                    (emit {:event :timer-entry :world w :n n :r r :o o :frame frame
                           :variant variant :value value})))))))

(defn timer-return [s {:keys [w n frame] :as action}]
  (let [row (get-in s [:env :native n])]
    (require! (and (cleanup/timer-resource? row) (= w (first (:owner row)))
                   (= #{frame} (:frames row)) (= frame [:timer-frame n 0]))
              ::not-timer-return {:action action})
    (timer-prune (assoc-in s [:env :native n :frames] #{}) n)))

(defn timer-handle-release [s {:keys [w n phase variant value] :as action}]
  (let [row (get-in s [:env :native n])]
    (require! (and (cleanup/timer-resource? row) (= w (first (:owner row)))
                   (not= :armed (:phase row))
                   (case phase :claim (= :release-pending (:handle row))
                         :returned (and (= :release-claimed (:handle row)) (#{:ok :error} variant)) false))
              ::not-timer-handle-release {:action action})
    (let [s (assoc-in s [:env :native n :handle]
                      (if (= :claim phase) :release-claimed (if (= :ok variant) :released :failed)))
          s (if (and (= :returned phase) (= :error variant))
              (emit s {:event :timer-fault :world w :n n :stage :release :value value}) s)]
      (timer-prune s n))))

(defn refresh-timer-anchors [s]
  (update-in s [:env :native]
             #(into {} (for [[n row] %]
                         [n (if (and (cleanup/timer-resource? row) (not (:retired? row)))
                              (assoc row :anchor (owner-chain s (first (:owner row)) (second (:owner row)))) row)]))))

(defn t07-complete
  "T7 complete current running copy; missing/stale completions are inert."
  [s {:keys [w r value] :or {value :result}}]
  (let [rr (run s w r) e (:spin rr)]
    (if (and (= :running (:status rr)) (= r (current s w e)))
      (let [s (-> s (assoc-in [:worlds w :entities e :completed?] true)
                  (assoc-in [:worlds w :entities e :dirty?] (boolean (:validation-lost? rr)))
                  (assoc-in [:worlds w :entities e :result] value)
                  (assoc-in [:worlds w :runs r :status] :completed)
                  (enqueue w {:completion e :debtor-world w :value value}))
            targets (fdep-targets (wr s w) e)
            s (reduce #(enqueue %1 %2 {:completion e :debtor-world w :value value}) s targets)
            preds (for [[p pr] (:runs (wr s w))
                        :when (and (= e (:spin pr)) (not= p r)
                                   (#{:completed :stale} (:status pr)))] p)
            s (reduce #(t10-supersede %1 {:w w :r %2}) s (sort-by pr-str preds))
            s (update-in s [:worlds w :entities]
                         #(into {} (remove (fn [[_ er]] (and (= r (:owner er))
                                                             (#{:timer :waiter} (:kind er)))) %)))]
        (rule-l s w)) s)))

(defn t08-deliver
  "T8 process a completion. Host-filter O12 is explicit data."
  [s {:keys [w e debtor-world value] :as a}]
  (require! (not= :mailbox (:kind (ent s (or debtor-world w) e))) ::unsupported-mailbox-publication {:w w :e e})
  (let [s (rule-l s w)
        dw (or debtor-world w) obligations (:obligations (wr s w))
        s (if (:dequeued? a) s
              (update-in s [:worlds w :queue]
                         (fn [queue]
                           (let [[prefix remaining] (split-with #(not (and (= e (:completion %))
                                                                           (= dw (:debtor-world %)))) queue)]
                             (into (vec prefix) (rest remaining))))))]
    (rule-l
     (reduce
      (fn [s [o ob]]
        (if (not= [:entity dw e] (:debtor ob)) s
            (if (= :host (first (:creditor ob)))
              (cond-> (if (and (= :causal-follow (get-in ob [:filter :mode]))
                               (contains? (:host-delivered s) [w o])) s
                          (cond-> (emit s {:event :host-delivery :world w :e e :o o
                                           :value value :causal? (= :causal-follow (get-in ob [:filter :mode]))})
                            (= :causal-follow (get-in ob [:filter :mode]))
                            (update :host-delivered (fnil conj #{}) [w o])))
                (or (not (:standing? ob)) (final? s dw e)) (end-obligation w o :delivered))
              (if (cancelling? s w o ob)
                (-> s (t06-resume {:w w :o o :value value}) (end-obligation w o :delivered))
                (if (and (:standing? ob) (= :consumed (:slot ob))
                         (not= :inherited (:status (run s w (nth (:creditor ob) 2)))))
                  (t09-reenter s {:w w :e (first (nth (:creditor ob) 2))
                                  :cause (if (= :track (:kind ob)) :track :reactive)
                                  :order (:order ob)})
                  (t06-resume s {:w w :o o :value value})))))) s obligations) w)))

(defn claim-owner-custody
  "Move current custody before owner rows or async dispatch can disappear."
  [s w owner]
  (let [holder (execution-holder w owner)]
    (reduce
     (fn [state k]
       (let [c (cap state k) [state id op] (allocate-custody-claim state c)
             cleanup-holder [:cleanup id]
             kind (if (= :open (:disposition c)) :discard (:kind c))
             claim {:cap k :holder cleanup-holder :origin holder
                    :anchor (mapv #(execution-holder w %) (butlast (owner-chain state w owner)))
                    :target-world (:world c) :kind kind :settlement-op op :phase :dispatch-pending}]
         (-> state (assoc-in [:custody :claims id] claim)
             (put-cap k (assoc c :holder cleanup-holder :holder-acquisition nil))
             (assoc-in [:env :cleanup-targets w id] {:target-world (:world c) :cap k :op op})
             (enqueue (:world c) {:custody-dispatch id :cap k :op op}))))
     s (sort-by pr-str (get-in s [:custody :by-holder holder] #{})))))

(defn t09-reenter
  "T9 successor generation, stale cleanup, and prefix adoption."
  [s {:keys [w e cause order] :or {cause :dirty order -1}}]
  (executable! s w)
  (let [r (current s w e) rr (run s w r)]
    (require! rr ::missing-run {:e e})
    (let [stales (for [[p pr] (:runs (wr s w))
                       :when (and (= e (:spin pr)) (= :stale (:status pr)))] p)
          s (reduce #(t10-supersede %1 {:w w :r %2}) s (sort-by pr-str stales))
          [s r2] (start-run s w e (:owner rr) cause)
          ;; Starting retires a dormant inherited run. Only a predecessor
          ;; still present after that teardown can donate prefix resources.
          previous (run s w r)
          s (if (and (#{:track :reactive} cause)
                     (or (:validation-lost? previous) (:dirty? (ent s w e))))
              (assoc-in s [:worlds w :runs r2 :validation-lost?] true) s)
          s (if (work? previous) (assoc-in s [:worlds w :runs r :status] :stale) s)
          s (reduce (fn [s [o ob]]
                      (if (not= [:run w r] (:creditor ob)) s
                          (if (and previous
                                   (or (and (= :track (:kind ob)) (<= (:order ob) order))
                                       (and (= :await-reactive (:kind ob)) (:standing? ob)
                                            (= :consumed (:slot ob)) (< (:order ob) order))))
                            (let [[dk dw de] (:debtor ob)]
                              (cond-> (assoc-in s [:worlds w :obligations o :creditor] [:run w r2])
                                (and (= :await-reactive (:kind ob)) (= :entity dk) (= w dw))
                                (adopt-call-target w de r2)))
                            (if (work? previous) (end-obligation s w o :creditor-cancelled) s))))
                    s (:obligations (wr s w)))
          s (update-in s [:worlds w :scopes]
                       #(into {} (for [[id sr] %]
                                   [id (if (and (= r (:parent sr)) (< (get sr :order 0) order))
                                         (assoc sr :parent r2) sr)])))
          s (reduce (fn [state k]
                      (let [c (cap state k) acquisition (:holder-acquisition c)]
                        (if (and previous (integer? acquisition) (< acquisition order))
                          (put-cap state k (assoc c :holder (execution-holder w r2))) state)))
                    s (get-in s [:custody :by-holder (execution-holder w r)] #{}))
          prefix (filter #(< (get-in s [:worlds w :entities % :order] 0) order)
                         (:creations previous))]
      (rule-l
       (reduce (fn [s child]
                 (-> s (assoc-in [:worlds w :entities child :owner] r2)
                     (cond-> (:creator (ent s w child))
                       (assoc-in [:worlds w :entities child :creator] r2))
                     (update-in [:worlds w :runs r2 :creations] conj child)
                     (update-in [:worlds w :runs r :creations] disj child)
                     (update-in [:worlds w :runs]
                                #(into {} (for [[id rr] %]
                                            [id (if (and (= child (:spin rr)) (= r (:owner rr)))
                                                  (assoc rr :owner r2) rr)]))))) s prefix) w))))

(defn end-run-links
  "Logical teardown; retirement keeps the owner row until descendants snapshot anchors."
  [s w r cause]
  (let [s (reduce (fn [s [o ob]] (if (= [:run w r] (:creditor ob))
                                   (end-obligation s w o :creditor-cancelled) s))
                  s (:obligations (wr s w)))]
    (-> s (update-in [:worlds w :runs] #(into {} (for [[id rr] %] [id (update rr :spawned disj r)])))
        (update-in [:env :native]
                   #(into {} (for [[n nr] %]
                               [n (if (and (= [w r] (:owner nr)) (not= :joined (:state nr))
                                           (not (or (cleanup/protected? nr) (cleanup/mailbox-callback? nr) (cleanup/timer-resource? nr))))
                                    (assoc nr :state :cancel-requested) nr)])))
        (emit {:event :run-exit :world w :r r :cause cause
               :t (if (= cause :superseded) :t10 :t11)}))))

(defn retain-cleanup-subtree [s w root]
  (if (or (get-in s [:model :cps-exit?]) (some cleanup/mailbox-callback? (vals (get-in s [:env :native]))))
    (cleanup/retain-subtree s w root
                            (into {} (for [[r _] (:runs (wr s w))] [r (owner-chain s w r)]))) s))

(defn- retire-run-body
  "§4.3 run retirement: close child scopes before logical teardown, then retain
  only physical evidence. Nested teardown reaches rule L at the outer boundary."
  [s w r cause logical-effects anchor]
  (let [rr (run s w r) chain (or anchor (owner-chain s w r))
        s (claim-owner-custody s w r)
        s (retain-cleanup-subtree s w r)
        s (update-in s [:env :native]
                     #(into {} (for [[n row] %]
                                 [n (if (and (cleanup/timer-resource? row) (= [w r] (:owner row)))
                                      (assoc row :retired? true :anchor chain) row)])))]
    (binding [*cascading?* true]
      (let [s (reduce #(t13-close-scope %1 {:w w :scope %2}) s
                      (sort-by pr-str (for [[id row] (:scopes (wr s w)) :when (= r (:parent row))] id)))
            s (logical-effects (end-run-links s w r cause))
            s (update-in s [:worlds w :runs] dissoc r)]
        (if (physical? s w r)
          (-> s
              (assoc-in [:worlds w :runs r]
                        (assoc rr :status :unwinding :owner nil :anchor chain :retired? true
                               :creations #{} :spawned #{} :pred nil :ancestors #{}))
              (update-in [:env :threads]
                         #(into {} (for [[th tr] %]
                                     [th (cond-> tr (and (= w (:world tr)) (= r (:run tr)))
                                                 (assoc :retired? true))])))
              (update-in [:env :native]
                         #(into {} (for [[n nr] %]
                                     [n (cond-> nr (= [w r] (:owner nr)) (assoc :retired? true))])))
              (update-in [:worlds w :runs]
                         #(into {} (for [[id row] %]
                                     [id (cond-> (update row :spawned disj r)
                                           (= r (:pred row)) (assoc :pred nil))])))
              (update-in [:worlds w :entities]
                         #(into {} (for [[id row] %]
                                     [id (cond-> row (= r (:creator row)) (assoc :creator nil))]))))
          s)))))

(defn retire-run
  "Retire once per synchronous cascade; keep the real row for frozen anchors.
   Entity release can revisit an executing ancestor through a different owner
   forest. Its entity effects still run, but the first Run exit cause wins."
  [s w r cause logical-effects anchor]
  (if (contains? *retiring-owners* [w r]) s
      (binding [*retiring-owners* (assoc *retiring-owners* [w r] (or anchor (owner-chain s w r)))]
        (retire-run-body s w r cause logical-effects anchor))))

(defn owner-release [s w e]
  ;; Entity lifetime dominates every run owner, including completed scopes (V03).
  (if (ent s w e)
    (let [s (if (= :mailbox (:kind (ent s w e)))
              (update-in s [:env :native]
                         #(into {} (for [[id row] %]
                                     [id (if (and (cleanup/mailbox-callback? row)
                                                  (= w (first (:owner row))) (= e (:allocation row)))
                                           (assoc row :retired? true) row)]))) s)
          s (if (= :mailbox (:kind (ent s w e)))
              (reduce (fn [s [o ob]]
                        (if (and (= [:entity w e] (:debtor ob)) (= :host (first (:creditor ob))))
                          (queue-mailbox-rejection s w e o
                                                   (if *release-cancellation* (:value *release-cancellation*)
                                                       :org.replikativ.spindel.engine.protocols/cancelled)) s))
                      s (:obligations (wr s w))) s)
          s (cond-> (assoc-in s [:worlds w :entities e :owner] nil)
              (= :spin (:kind (ent s w e))) (assoc-in [:worlds w :entities e :dirty?] true))
          runs (vec (for [[r rr] (:runs (wr s w))
                          :when (and (= e (:spin rr))
                                     (#{:running :parked :inherited} (:status rr)))] r))
          s (reduce #(t11-cancel %1 {:w w :r %2}) s (sort-by pr-str runs))
          completed (vec (for [[r rr] (:runs (wr s w))
                               :when (and (= e (:spin rr))
                                          (#{:completed :stale} (:status rr)))] r))
          s (reduce #(t10-supersede %1 {:w w :r %2}) s (sort-by pr-str completed))]
      (reduce (fn [s [o ob]]
                (let [consumer [(if (= :host (first (:creditor ob))) :host :obligation) o]
                      control (cleanup/mailbox-control s w e e)
                      reservation (get-in control [:reservations consumer])
                      r (nth (:creditor ob) 2 nil)
                      s (if (and control (= :run (first (:creditor ob)))
                                 (not (#{:claimed :entered} (:state reservation))))
                          (cond-> (cleanup/detach-mailbox-consumer s w e e consumer)
                            (= :running (:status (run s w r)))
                            (assoc-in [:worlds w :runs r :status] :parked)) s)
                      s (if (= :run (first (:creditor ob)))
                          (t06-resume s {:w w :o o :value (if *release-cancellation*
                                                            (:value *release-cancellation*) ::cancelled)}) s)]
                  (end-obligation s w o :cancel-delivered)))
              s (filter #(= [:entity w e] (:debtor (val %))) (:obligations (wr s w))))) s))

(defn release-owned [s w scope]
  (reduce #(owner-release %1 w %2) s
          (sort-by pr-str (for [[e er] (:entities (wr s w)) :when (= scope (:owner er))] e))))

(defn remove-request [event v o]
  (cond
    (and (= v (:creditor-world event)) (= o (:o event)) (:start-for event)) nil
    (= v (:join-bundle event))
    (let [members (dissoc (:members event) o)]
      (when (seq members) (assoc event :members members :debtors (set (map :debtor (vals members))))))
    :else event))

(defn retire-request [s w v o]
  (-> s (update-in [:worlds w :queue] #(vec (keep (fn [event] (remove-request event v o)) %)))
      (update-in [:env :outside]
                 #(vec (keep (fn [held]
                               (if (= w (:w held))
                                 (when-let [event (remove-request (:event held) v o)] (assoc held :event event))
                                 held)) %)))))

(defn cancel-foreign-debtor
  ([s w v o] (cancel-foreign-debtor s w v o nil))
  ([s w v o cancellation]
  ;; These are this transaction's own rows, so no releasing/cleanup handshake.
   (let [ob (get-in s [:worlds v :obligations o]) e (nth (:debtor ob) 2)
         s (-> s (retire-request w v o)
               (update-in [:worlds w :fdeps] disj [e v o])
               (enqueue v (cond-> {:cancelled o}
                            cancellation (assoc :value (:value cancellation)))))
         other? (some (fn [[other candidate]]
                        (and (not= o other) (= [:entity w e] (:debtor candidate))
                             (= :run (first (:creditor candidate)))
                             (= :inherited (:status (run s v (nth (:creditor candidate) 2))))
                             (not (pending-start? s v other candidate))
                             (not (cancelling? s v other candidate))))
                      (:obligations (wr s v)))]
     (if other? s
         (update-in s [:worlds w :fdeps]
                    #(set (keep (fn [[tag target d :as fd]]
                                  (if (and (= :bundle tag) (= v target))
                                    (when (seq (disj d e)) [:bundle v (disj d e)]) fd)) %)))))))

(defn t10-supersede
  "T10 retire completed/stale runs at successor completion or owner release.
  Release every owned entity, including entities absent from creations(r)."
  [s {:keys [w r]}]
  (if-let [rr (run s w r)]
    (let [chain (owner-chain s w r)]
      (require! (#{:completed :stale} (:status rr)) ::not-predecessor {:r r})
      (rule-l
       (retire-run
        s w r :superseded
        (fn [s]
          (let [owned (for [[c cr] (:runs (wr s w)) :when (= r (:owner cr))] c)
                s (reduce #(t11-cancel %1 {:w w :r %2 :anchor (into [%2] chain)}) s (sort-by pr-str owned))
                s (update-in s [:worlds w :entities]
                             #(into {} (remove (fn [[_ er]]
                                                 (and (= r (:owner er))
                                                      (#{:cache-row :keyed-entry} (:kind er)))) %)))]
            (release-owned s w r)))
        chain) w)) s))

(defn t11-cancel
  "T11 retire a copy, fail debtor obligations, recursively release owned runs."
  [s {:keys [w r anchor] :as action}]
  (if-let [rr (when (not= :unwinding (:status (run s w r))) (run s w r))]
    (let [chain (or anchor (owner-chain s w r))
          e (:spin rr) current? (= r (current s w e))
          cancellation (or (when (contains? action :cancel-value) {:value (:cancel-value action)})
                           *release-cancellation*)]
      (rule-l
       (retire-run
        s w r :cancelled
        (fn [s]
          (let [children (for [[c cr] (:runs (wr s w)) :when (= r (:owner cr))] c)
                s (reduce #(t11-cancel %1 {:w w :r %2 :anchor (into [%2] chain)}) s (sort-by pr-str children))
                s (if current?
                    (reduce
                     (fn [s [v o ob]]
                       (if (not= v w)
                         (cancel-foreign-debtor s w v o cancellation)
                         (let [s (if (= :run (first (:creditor ob)))
                                   (t06-resume s {:w v :o o :value (if cancellation (:value cancellation) ::cancelled)}) s)]
                           (end-obligation s v o :cancel-delivered cancellation))))
                     s (cond->> (for [[v world] (:worlds s) [o ob] (:obligations world)
                                      :when (and (= [:entity w e] (:debtor ob))
                                                 (or (= w v) (known-foreign-obligation? s w v o ob)))] [v o ob])
                         cancellation (sort-by #(second (second %))))) s)
                s (if (and current? (= :stale (:status (run s w (:pred rr)))))
                    (t10-supersede s {:w w :r (:pred rr)}) s)
                s (release-owned s w r)]
            (if (ent s w e) (assoc-in s [:worlds w :entities e :dirty?] true) s)))
        chain) w)) s))

(defn cancel-computation
  "Commit public cancellation before retiring only the target's existing runs."
  [s {:keys [w e tok value]}]
  (executable! s w)
  (require! (= :open (:admission (wr s w))) ::not-admitted {:world w})
  (let [handle (get-in s [:env :handles tok]) old (ent s w e)]
    (require! (and handle (= e (:spin handle)) (:reachable? handle))
              ::unknown-handle {:w w :e e :tok tok})
    (require! (not (contains? (:dropped handle) w)) ::idle-cache-released {:w w :e e :tok tok})
    (require! (or (nil? old) (= :spin (:kind old))) ::not-computation {:w w :e e})
    (let [s (if old s (assoc-in s [:worlds w :entities e] (spin-row s w e (:root (wr s w)))))
          s (touch s w e tok)]
      (if (contains? (ent s w e) :cancelled-completion) s
          (let [r (current s w e)
                dirty? (boolean (or (:dirty? (ent s w e)) (:validation-lost? (run s w r))))
                targets (vec (sort-by second > (for [[id row] (:runs (wr s w)) :when (= e (:spin row))] id)))
                publication? (fn [event] (and (= e (:completion event)) (= w (:debtor-world event))))
                s (-> s
                      (assoc-in [:worlds w :entities e :completed?] true)
                      (assoc-in [:worlds w :entities e :result] value)
                      (assoc-in [:worlds w :entities e :cancelled-completion] {:run r :result value})
                      (update :worlds #(into {} (for [[v world] %]
                                                  [v (if (some publication? (:queue world))
                                                       (update world :queue (fn [queue] (vec (remove publication? queue))))
                                                       world)])))
                      (update-in [:env :outside] #(vec (remove (fn [held] (publication? (:event held))) %))))
              ;; Reserve before teardown, preserving any live protected wait.
                s (reduce (fn [s id]
                            (let [s (retain-cleanup-subtree s w id) n (cleanup/ticket w id)
                                  ticket (get-in s [:env :native n])]
                              (if (and (cleanup/exit? ticket) (not (contains? ticket :cancel-value)))
                                (assoc-in s [:env :native n :cancel-value] value) s))) s targets)
              ;; One public transaction retires the entire pre-action batch.
              ;; Intermediate Rule L must not supersede an older basis before
              ;; its explicit T11 cancellation is applied.
                s (binding [*cascading?* true]
                    (reduce #(t11-cancel %1 {:w w :r %2 :cancel-value value}) s targets))
              ;; There may be incoming observers but no run (an idle cache).
                s (reduce (fn [s [v o ob]]
                            (if (not= v w) (cancel-foreign-debtor s w v o {:value value})
                                (let [s (if (= :run (first (:creditor ob)))
                                          (t06-resume s {:w w :o o :value value}) s)]
                                  (end-obligation s w o :cancel-delivered {:value value}))))
                          s (sort-by #(second (second %))
                                     (for [[v world] (:worlds s) [o ob] (:obligations world)
                                           :when (and (= [:entity w e] (:debtor ob))
                                                      (or (= w v) (known-foreign-obligation? s w v o ob)))] [v o ob])))]
            (assoc-in s [:worlds w :entities e :dirty?] dirty?))))))

(defn t12-open-scope
  "T12 open explicit, supervisor, render or SCI scope."
  [s {:keys [w scope parent kind order] :or {kind :explicit order 0}}]
  (live! s w)
  (require! (explicit-scope-id? scope) ::invalid-scope-id {:scope scope})
  (require! (and (>= (nth scope 2) (:next-scope (wr s w)))
                 (nil? (get-in s [:worlds w :scopes scope]))
                 (not= scope parent)) ::scope-id-reused {:scope scope})
  (require! (open? s w parent) ::closed-scope {:parent parent})
  (-> s
      (assoc-in [:worlds w :next-scope] (inc (nth scope 2)))
      (update-in [:worlds w :scope-balance] inc)
      (assoc-in [:worlds w :scopes scope]
                (cond-> {:kind kind :parent parent :status :open}
                  (run s w parent) (assoc :order order)))))

(defn close-owned [s w scope]
  (if (contains? *retiring-owners* [w scope]) s
      (let [root? (= scope (:root (wr s w)))]
        (binding [*retiring-owners* (assoc *retiring-owners* [w scope] (owner-chain s w scope))]
          (rule-l
           (binding [*cascading?* true]
             ;; Explicit Scope ancestry can disappear during collateral parent
             ;; retirement. Root has no removable ancestor and retains its old
             ;; publication order after child cancellation.
             (let [s (if root? s (claim-owner-custody s w scope))
                   s (retain-cleanup-subtree s w scope)
                   children (for [[c cr] (:scopes (wr s w))
                                  :when (and (= scope (:parent cr)) (= :open (:status cr)))] c)
                   s (reduce #(close-owned %1 w %2) s (sort-by pr-str children))
                   runs (for [[r rr] (:runs (wr s w)) :when (= scope (:owner rr))] r)
                   s (reduce #(t11-cancel %1 {:w w :r %2}) s (sort-by pr-str runs))
                   s (if root? (claim-owner-custody s w scope) s)]
               (cond-> (release-owned s w scope)
                 (not root?)
                 (-> (update-in [:worlds w :scopes] dissoc scope)
                     (update-in [:worlds w :scope-balance] dec))))) w)))))

(defn t13-close-scope
  "T13 idempotent close, including implicit fork discard."
  [s {:keys [w scope]}]
  (require! (or (explicit-scope-id? scope) (= scope [:root w]))
            ::invalid-scope-id {:scope scope})
  (cond (= :released (:status (wr s w))) s
        (= scope (:root (wr s w))) (t34-release-world s {:w w})
        (not (open? s w scope)) s
        :else (close-owned s w scope)))

(defn t14-pin
  "T14 root-held pin reason leaves ownership unchanged."
  [s {:keys [w e pin?]}]
  (if (or (= :released (:status (wr s w))) (and (not pin?) (nil? (ent s w e)))) s
      (do (require! (ent s w e) ::missing-entity {:e e})
          (when pin? (live! s w))
          (-> s (update-in [:worlds w :pins] (if pin? conj disj) e)
              (rule-l w)))))

(defn t15-cancel-world-work
  "T15 cancel all work, excluding dormant inherited copies."
  [s {:keys [w]}]
  (reduce #(t11-cancel %1 {:w w :r %2}) s
          (sort-by pr-str (for [[r rr] (:runs (wr s w)) :when (work? rr)] r))))

(defn t16-handle-unreachable
  "T16 environment reachability loss; notifications can be delayed/lost."
  [s {:keys [tok]}]
  (require! (get-in s [:env :handles tok :reachable?]) ::already-unreachable {:tok tok})
  (let [{:keys [spin touched]} (get-in s [:env :handles tok])]
    (-> s (assoc-in [:env :handles tok :reachable?] false)
        (update-in [:env :gc] (fnil into [])
                   (for [w touched :when (and ((:registry s) w) (ent s w spin))]
                     {:t :t17 :w w :e spin :tok tok})))))

(defn t17-gc-notify
  "T17 stale and duplicate token notifications are inert."
  [s {:keys [w e tok]}]
  (require! (false? (get-in s [:env :handles tok :reachable?])) ::reachable-handle {:tok tok})
  (let [s (update-in s [:env :gc] #(vec (remove (fn [a] (= [w e tok] [(:w a) (:e a) (:tok a)])) %)))]
    (if (contains? (:tokens (ent s w e)) tok)
      (-> s (update-in [:worlds w :entities e :tokens] disj tok) (rule-l w)) s)))

(defn t18-release-idle-caches
  "T18 deterministic idle cache release, poisoning every touched incarnation."
  [s {:keys [w es]}]
  (let [s (rule-l s w)]
    (rule-l
     (reduce (fn [s e]
               (if (idle? s w e)
                 (-> (reduce #(update-in %1 [:env :handles %2 :dropped] conj w)
                             s (:tokens (ent s w e)))
                     (assoc-in [:worlds w :entities e :tokens] #{})) s))
             s (or es (keys (:entities (wr s w))))) w)))

(defn copy-evidence
  "Capture phase and value envelopes once, before any copy is installed."
  [s w]
  (into {} (for [[o ob] (:obligations (wr s w))]
             [o {:phase (cond (cancelling? s w o ob) :cancelling
                              (pending-start? s w o ob) :pending-start
                              :else :admitted)
                 :cancelled (first (filter #(= o (:cancelled %)) (pending-events s w)))
                 :completions (vec (filter #(and (= (nth (:debtor ob) 2 nil) (:completion %))
                                                 (= (second (:debtor ob)) (get % :debtor-world w)))
                                           (pending-events s w)))}])))

(defn copy-queue [evidence obligations]
  (let [events (distinct
                (sort-by :seq
                         (mapcat (fn [[o ob]]
                                   (let [{:keys [cancelled completions]} (get evidence o)]
                                     (concat (when cancelled [cancelled])
                                             (map #(assoc % :debtor-world (second (:debtor ob))) completions))))
                                 obligations)))]
    (mapv #(assoc %1 :seq %2) events (range 1 (inc (count events))))))

(defn register-bundles [s v evidence join?]
  (let [inherited (for [[o ob] (:obligations (wr s v))
                        :let [[kind dw e] (:debtor ob)]
                        :when (and (= :entity kind) (not= dw v) (= :run (first (:creditor ob)))
                                   (= :inherited (:status (run s v (nth (:creditor ob) 2)))))]
                    [dw e o ob])
        s (reduce (fn [s [dw e o _]]
                    (case (get-in evidence [o :phase])
                      :cancelling s
                      :pending-start (enqueue s dw {:start-for e :creditor-world v :o o})
                      (if join? s (add-fdep s v o)))) s inherited)]
    (if-not join? s
            (reduce (fn [s [dw rows]]
                      (enqueue s dw {:join-bundle v :debtors (set (map second rows))
                                     :members (into {} (for [[_ e o ob] rows]
                                                         [o {:debtor e :source-world (:source-world ob) :source-o o}]))}))
                    s (group-by first (filter #(= :admitted (get-in evidence [(nth % 2) :phase])) inherited))))))

(defn attach-world [s w v scope k systems child evidence join? order]
  (require! (not (contains? (:known-worlds s) v)) ::world-id-reused {:world v})
  (fresh-cap! s k)
  (when (run s w scope)
    (require! (or (= :exact-run order) (and (integer? order) (not (neg? order))))
              ::missing-creator-order {:scope scope :order order}))
  (let [last-seq (reduce max (get child :seq 0) (keep :seq (:queue child)))
        s (-> s (assoc-in [:worlds v] child)
              (cond-> (> last-seq (get child :seq 0)) (assoc-in [:clocks v] last-seq))
              (update :generation-clock #(reduce (fn [cl [r rr]]
                                                   (update cl [v (:spin rr)] (fnil max 0) (second r)))
                                                 (or % {}) (:runs child)))
              (update :registry conj v)
              (update :known-worlds conj v) (assoc-in [:lineages v] (:lineage child))
              (assoc-in [:worlds w :entities [:fork v]] (row :fork scope))
              (put-cap k {:world v :scope systems :holder (execution-holder w scope)
                          :holder-acquisition (when (run s w scope) order)
                          :disposition :open :published? (not= :fenced (:admission child))
                          :op nil :pred nil :successors []
                          :bases (into {} (for [sys systems] [sys [:base v sys]]))}))]
    (-> (reduce (fn [s [e er]]
                  (let [s (if (= :spin (:kind er))
                            (update-in s [:worlds v :entities e :tokens] set/union (covering-tokens s v e)) s)]
                    (reduce #(touch %1 v e %2) s (:tokens er))))
                s (:entities child))
        (cond-> (not join?) (register-bundles v evidence false))
        (rule-l v))))

(defn copy-row [row w origin]
  (assoc row :origin origin :source-world w))
(defn copy-obligation [ob w v]
  (let [endpoint (fn [[kind dw id :as end]]
                   (if (and (= kind :run) (= w dw)) [kind v id] end))]
    (cond-> (-> (copy-row ob w :inherited) (update :creditor endpoint))
      (#{:timer :external} (:kind ob)) (assoc :token nil :dormant? true)
      (= :host (first (:creditor ob))) (assoc :cont nil :descriptor? true))))
(defn copy-host? [ob]
  (or (not= :host (first (:creditor ob)))
      (= :causal-follow (get-in ob [:filter :mode]))))

(defn- deferred-world? [s w world]
  (or (some #(#{:deferred :mailbox} (:kind %)) (vals (:entities world)))
      (some (fn [[key cell]] (and (= w (first key)) (#{:deferred :mailbox} (:kind cell))))
            (get-in s [:env :cleanup-cells]))
      (some #(and (= w (first (:owner %))) (or (:operation %) (cleanup/mailbox-callback? %) (cleanup/timer-resource? %))) (vals (get-in s [:env :native])))))

(defn t19-fork-following
  "T19 persistent inherited bundles, expanded here for logical-row checking."
  [s {:keys [w v k scope systems acceptance] :or {systems #{:a :b}}}]
  (live! s w)
  (require! (not (deferred-world? s w (wr s w))) ::unsupported-deferred-fork {:w w})
  (require! (open? s w scope) ::closed-scope {:scope scope})
  (let [order (holder-acquisition! s (execution-holder w scope) acceptance)
        child (assoc (world-row v w :following (get-in s [:worlds w :lineage :root])) :seq (get-in s [:worlds w :seq] 0))
        copies (into {} (for [[r rr] (:runs (wr s w)) :when (= :parked (:status rr))]
                          [r (assoc (dissoc (copy-row rr w :inherited) :cps-entered?)
                                    :status :inherited :owner (:root child))]))
        scopes (loop [parents (set (keys copies)) found {}]
                 (let [children (into {} (for [[id sr] (:scopes (wr s w))
                                               :when (contains? parents (:parent sr))]
                                           [id (copy-row sr w :inherited)]))]
                   (if (empty? children) found
                       (recur (set (keys children)) (merge found children)))))
        owners (into (set (keys copies)) (keys scopes))
        es (set (concat (map :spin (vals copies))
                        (for [[e er] (:entities (wr s w))
                              :when (or (contains? owners (:owner er)) (contains? copies (:creator er)))] e)))
        copies (into {} (for [[r rr] copies]
                          [r (-> rr (update :creations set/intersection es)
                                 (update :spawned set/intersection (set (keys copies))))]))
        entities (into {} (for [e es :let [er (ent s w e)]]
                            [e (cond-> (assoc (copy-row er w :inherited) :owner
                                              (if (contains? owners (:owner er)) (:owner er) (:root child)))
                                 (= :fork (:kind er)) (assoc :reference? true))]))
        obs (into {} (for [[o ob] (:obligations (wr s w))
                           :when (or (contains? copies (nth (:creditor ob) 2 nil))
                                     (and (= :host (first (:creditor ob)))
                                          (contains? es (nth (:debtor ob) 2 nil)) (copy-host? ob)))]
                       [o (cond-> (copy-obligation ob w v)
                            (= :host (first (:creditor ob))) (assoc :debtor [:entity v (nth (:debtor ob) 2)]))]))]
    (let [evidence (copy-evidence s w)]
      (attach-world s w v scope k systems
                    (assoc child :runs copies :entities entities :obligations obs
                           :scopes (merge (:scopes child) scopes)
                           :next-scope (:next-scope (wr s w)) :scope-balance (count scopes)
                           :queue (copy-queue evidence obs)) evidence false order))))

(defn t20-cut-fence
  "T20 fence participants, holding later arrivals outside."
  [s {:keys [c participants scope mode deadline coordinator]
      :or {deadline 1 coordinator :coordinator mode :frozen}}]
  (require! (= 1 (count (:worlds participants))) ::one-engine-world {:participants participants})
  (require! (not-any? #(and (active-cuts (:phase %))
                            (seq (set/intersection (:systems participants) (get-in % [:participants :systems]))))
                      (vals (:cuts s))) ::cut-conflict {:participants participants})
  (doseq [w (:worlds participants)]
    (live! s w)
    (require! (not-any? #(and (active-cuts (:phase %))
                              (contains? (get-in % [:participants :worlds]) w))
                        (vals (:cuts s))) ::cut-conflict {:w w}))
  (let [w (first (sort (:worlds participants)))]
    (require! (open? s w scope) ::closed-scope {:scope scope})
    (-> (reduce #(assoc-in %1 [:worlds %2 :admission] :fenced) s (:worlds participants))
        (update :cut-allocations (fnil inc 0))
        (assoc-in [:cuts c] {:participants participants :phase :fenced :basis nil
                             :child nil :requester scope :deadline deadline :mode mode
                             :coordinator coordinator
                             :fence-seq (into {} (for [w (:worlds participants)]
                                                   [w (max (get-in s [:worlds w :seq] 0) (get-in s [:clocks w] 0))]))}))))

(defn cut-blockers
  "Readiness diagnostics, without executing any admitted step."
  [s c]
  (let [cut (get-in s [:cuts c]) worlds (get-in cut [:participants :worlds])]
    {:running (vec (for [w worlds [r rr] (:runs (wr s w)) :when (cut-busy? rr)] [w r]))
     :admitted (vec (for [w worlds ev (:queue (wr s w))
                          :when (<= (:seq ev) (get-in cut [:fence-seq w]))] [w ev]))
     :native (vec (for [[n nr] (get-in s [:env :native])
                        :when (and (worlds (first (:owner nr))) (not= :joined (:state nr))
                                   (not (:boundary? nr)))] n))}))

(defn t20q-cut-fence
  "T20q is atomic T20 + readiness. Refusals roll back the tentative fence
  (T25), retaining the model's unchanged-state refusal convention."
  [s a]
  (let [fenced (try (t20-cut-fence s a)
                    (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) e
                      (refuse ::cut-refused {:cause (dissoc (ex-data e) :state)})))
        uncontrolled (set/intersection (get-in a [:participants :systems])
                                       (get-in s [:model :uncontrolled-systems] #{}))
        blockers (cut-blockers fenced (:c a))]
    (when (or (seq uncontrolled) (some seq (vals blockers)))
      ;; Roll back before reporting the refusal. The enclosing atomic step
      ;; discards this failed coordinator record along with its allocation.
      (t25-cut-fail fenced {:c (:c a)})
      (if (seq uncontrolled)
        (refuse ::uncontrolled-writer {:systems uncontrolled})
        (refuse ::not-quiescent blockers)))
    (-> fenced (assoc-in [:cuts (:c a) :protocol] :p1q)
        (assoc-in [:cuts (:c a) :phase] :ready))))

(defn t21-cut-drain
  "T21 readiness only after admitted queue, running work and native boundaries drain."
  [s {:keys [c body]}]
  (require! (not= :p1q (get-in s [:cuts c :protocol])) ::no-drain {:c c})
  (require! (= :fenced (get-in s [:cuts c :phase])) ::cut-phase {:c c})
  (let [worlds (get-in s [:cuts c :participants :worlds])
        w (first worlds) ev (first (:queue (wr s w)))
        _ (when body
            (require! (and (worlds (:w body)) (#{:t05 :t06 :t07 :t08 :t09 :t10 :t11} (:t body)))
                      ::not-admitted {:body body}))
        _ (when (and (not body) ev)
            (require! (<= (:seq ev) (get-in s [:cuts c :fence-seq w])) ::past-fence {:event ev}))
        s (cond body (step s body)
                ev (step s {:t :queued :w w})
                :else s)
        ready? (every? #(and (not-any? cut-busy?
                                       (vals (:runs (wr s %))))
                             (empty? (:queue (wr s %)))
                             (every? (fn [n] (or (not= % (first (:owner n)))
                                                 (= :joined (:state n)) (:boundary? n)))
                                     (vals (get-in s [:env :native])))) worlds)]
    (if ready? (assoc-in s [:cuts c :phase] :ready) s)))

(defn t22-cut-capture
  "T22 own-event exclusive acquisition, ordered by component world then id."
  [s {:keys [c timeout?]}]
  (let [cut (get-in s [:cuts c]) th (:coordinator cut)
        components (vec (sort (get-in cut [:participants :components])))
        thread (get-in s [:env :threads th])]
    (require! (= :ready (:phase cut)) ::cut-phase {:c c})
    (require! (not-any? #(deferred-world? s % (wr s %)) (get-in cut [:participants :worlds]))
              ::unsupported-deferred-fork {:c c})
    (require! (and (empty? (:read-permits thread)) (nil? (:run thread)))
              ::permit-held {:thread th})
    (require! (not timeout?) ::permit-timeout {:c c})
    (require! (not-any? #(seq (set/intersection (set components) (:read-permits %)))
                        (vals (get-in s [:env :threads]))) ::permit-busy {:c c})
    (require! (not-any? #(seq (set/intersection (set components) (set (:excl-permits %))))
                        (vals (get-in s [:env :threads]))) ::permit-busy {:c c})
    (-> s (assoc-in [:env :threads th :excl-permits] components)
        (assoc-in [:cuts c :phase] :captured)
        (assoc-in [:cuts c :basis]
                  (into {} (for [w (get-in cut [:participants :worlds])]
                             [w (assoc (wr s w) :copy-evidence (copy-evidence s w)
                                       :held (vec (filter #(= w (:w %)) (get-in s [:env :outside]))))])))
        (emit {:event :exclusive :thread th :read-permits (:read-permits thread)
               :components components}))))

(defn copy-basis
  "T23 copy a single engine world. Multi-world engine identity merge is unspecified."
  [s basis w v mode]
  (require! (not (deferred-world? s w (get basis w))) ::unsupported-deferred-fork {:w w})
  (let [base (get basis w) root (:root base)
        scope-id #(if (= root %) [:root v] %)
        endpoint (fn [[kind dw id :as end]]
                   (if (and (#{:entity :run} kind) (= w dw)) [kind v id] end))
        replaced (-> base
                     (assoc :root [:root v])
                     (update :scopes #(into {} (for [[id sr] %]
                                                 [(scope-id id) (cond-> (-> (copy-row sr w :inherited) (update :parent scope-id))
                                                                  (= id root) (assoc :kind :fork))])))
                     (update :entities #(into {} (for [[id er] %]
                                                   [id (-> (copy-row er w :inherited) (update :owner scope-id)
                                                           (cond-> (= :fork (:kind er)) (assoc :reference? true)))])))
                     (update :runs #(into {} (for [[id rr] %]
                                               [id (update rr :owner scope-id)])))
                     (update :obligations #(into {} (for [[id ob] %]
                                                      [id (-> ob (update :debtor endpoint)
                                                              (update :creditor endpoint))])))
                     (update :queue #(mapv (fn [ev] (cond-> ev (= w (:debtor-world ev))
                                                            (assoc :debtor-world v))) %)))
        parked (set (for [[r rr] (:runs base) :when (= :parked (:status rr))] r))
        copied (-> replaced (assoc :id v :status :live :admission :fenced :seal-seq nil :fdeps #{} :releasing #{})
                   (dissoc :copy-evidence :held)
                   (assoc :lineage {:parent w :root (get-in base [:lineage :root])
                                    :mode mode :cut nil :basis nil})

                   (update :runs #(into {} (for [[r rr] %]
                                             [r (cond-> (dissoc (copy-row rr w :inherited) :cps-entered?) (parked r)
                                                        (assoc :status :inherited :origin :inherited))])))
                   (update :obligations
                           #(into {} (for [[id ob] % :when (copy-host? ob)]
                                       [id (cond-> (copy-row ob w :inherited)
                                             (#{:timer :external} (:kind ob)) (assoc :token nil :dormant? true)
                                             (= :host (first (:creditor ob))) (assoc :cont nil :descriptor? true))]))))]
    (let [copied (assoc copied :queue (copy-queue (:copy-evidence base) (:obligations copied)))]
      (wr (rule-l (assoc-in s [:worlds v] copied) v) v))))

(defn t23-cut-attach
  "T23 attach a fenced logical basis with value-only causal descriptors."
  [s {:keys [c v k mode acceptance] :or {mode :frozen}}]
  (let [cut (get-in s [:cuts c]) worlds (get-in cut [:participants :worlds])
        w (first (sort worlds))]
    (require! (= :captured (:phase cut)) ::cut-phase {:c c})
    (require! (not-any? #(deferred-world? s % (get-in cut [:basis %])) worlds)
              ::unsupported-deferred-fork {:c c})
    (require! (= 1 (count worlds)) ::ambiguous-multi-world-basis {:worlds worlds})
    (let [child (-> (copy-basis s (:basis cut) w v mode)
                    (assoc-in [:lineage :cut] c)
                    (assoc-in [:lineage :basis] (:basis cut)))
          s (-> (attach-world s w v (:requester cut) k
                              (get-in cut [:participants :systems]) child
                              (get-in cut [:basis w :copy-evidence]) true
                              (holder-acquisition! s (execution-holder w (:requester cut)) acceptance))
                (assoc-in [:cuts c :phase] :attached) (assoc-in [:cuts c :child] v))]
      s)))

(defn release-cut [s c phase]
  (let [cut (get-in s [:cuts c]) participants (get-in cut [:participants :worlds])
        s (reduce #(assoc-in %1 [:worlds %2 :admission]
                             (if (= :sealed (:status (wr %1 %2))) :fenced :open)) s participants)
        outside (get-in s [:env :outside])]
    (-> (reduce (fn [s ev] (if (participants (:w ev))
                             (update-in s [:worlds (:w ev) :queue] conj (:event ev)) s)) s outside)
        (assoc-in [:env :outside] (vec (remove #(participants (:w %)) outside)))
        (assoc-in [:env :threads (:coordinator cut) :excl-permits] [])
        (assoc-in [:cuts c :phase] phase))))

(defn t24-cut-release
  "T24 make the child executable and issue its cross-world copy requests.
  Enqueue rejects released debtors atomically with ::released in the child."
  [s {:keys [c e] :or {e [:entry 0]}}]
  (require! (= :attached (get-in s [:cuts c :phase])) ::cut-phase {:c c})
  (let [v (get-in s [:cuts c :child]) s (release-cut s c :released)
        s (reduce (fn [s [k _]] (assoc-in s (conj (cap-path s k) :published?) true))
                  s (caps-of s v))
        s (assoc-in s [:worlds v :admission] :open)
        s (assoc-in s [:worlds v :entities e] (row :spin (:root (wr s v))))]
    (register-bundles (first (start-run s v e (:root (wr s v)) :entrypoint)) v
                      (get-in s [:cuts c :basis (first (keys (get-in s [:cuts c :basis]))) :copy-evidence]) true)))

(defn t25-cut-fail
  "T25 deadline/refusal: drop partial child, keep native ownership."
  [s {:keys [c]}]
  (let [cut (get-in s [:cuts c]) v (:child cut)]
    (require! (active-cuts (:phase cut)) ::cut-phase {:c c})
    (let [s (release-cut s c :failed)]
      (if-not v s
              (-> (reduce (fn [s [o ob]]
                            (emit s {:event :obligation-exit :world v :o o :ob ob :cause :creditor-cancelled}))
                          s (:obligations (wr s v)))
                  (update-in [:worlds (first (get-in cut [:participants :worlds])) :entities] dissoc [:fork v])
                  (update :worlds dissoc v) (update :registry disj v)
                  (as-> state (reduce remove-cap state (map first (caps-of state v)))))))))

(defn current-cap! [s k expected]
  (let [cap (cap s k)]
    (require! (expected (:disposition cap)) ::stale-capability {:k k}) cap))

(defn t26-seal
  "T26 refuse nonquiescent merge, else cancel when requested and seal."
  [s {:keys [k op kind force caller] :or {kind :merge}}]
  (let [cap (current-cap! s k #{:open}) w (:world cap)]
    (require! (:published? cap) ::unpublished-capability {:k k})
    (require! (wr s w) ::missing-world {:world w})
    (authenticate-holder! s k caller)
    (when (= :cleanup (first caller))
      (let [claim (get-in s [:custody :claims (second caller)])]
        (require! (and (= k (:cap claim)) (= op (:settlement-op claim)) (= kind (:kind claim)))
                  ::invalid-custody-claim {:k k :op op})))
    (fresh-operation! s op (when (= :cleanup (first caller)) (second caller)))
    (require! (wr s w) ::missing-world {:world w})
    (when (and (= :merge kind) (not force) (not (quiescent? s w)))
      (refuse ::not-quiescent {:world w :runs (:runs (wr s w)) :scopes (:scopes (wr s w))}))
    (let [s (reduce (fn [s [c cut]]
                      (if (and (active-cuts (:phase cut))
                               (contains? (get-in cut [:participants :worlds]) w))
                        (t25-cut-fail s {:c c}) s)) s (:cuts s))
          ;; Commit operation identity before cancellation can retire a Run
          ;; that itself holds this authority and move it into cleanup custody.
          s (-> s (assoc-in (into (cap-path s k) [:disposition]) :sealed)
                (assoc-in (into (cap-path s k) [:op]) op)
                (assoc-in (into (cap-path s k) [:kind]) kind))
          s (if (or force (= :discard kind)) (t15-cancel-world-work s {:w w}) s)]
      (-> s (assoc-in [:worlds w :status] :sealed)
          (assoc-in [:worlds w :admission] :fenced)
          (assoc-in [:worlds w :seal-seq] (max (get-in s [:worlds w :seq] 0) (get-in s [:clocks w] 0)))
          (assoc-in (into (cap-path s k) [:disposition]) :sealed)
          (assoc-in (into (cap-path s k) [:op]) op)
          (assoc-in (into (cap-path s k) [:kind]) kind)))))

(defn t27-prepare
  "T27 durable ordered settlement, bases and payload identity."
  [s {:keys [k op steps bases payload]}]
  (let [cap (current-cap! s k #{:sealed}) w (:world cap)]
    (require! (= op (:op cap)) ::changed-operation {:k k :op op})
    (require! (and (quiescent? s w) (joined? s w)) ::not-joined {:world w})
    (require! (not (record s op)) ::op-exists {:op op})
    (-> s (assoc-in (if (:durable? cap) [:durable :records op] [:records op])
                    {:op op :cap k :kind (:kind cap) :payload-hash payload
                     :steps (mapv #(merge {:status :pending :witness nil :compensation? false
                                           :effect-id [op (:id %)]} %) steps)
                     :bases bases :effects-released? false})
        (assoc-in (into (cap-path s k) [:disposition]) :settling)
        (assoc-in (into (cap-path s k) [:op]) op))))

(defn t28-settlement-step
  "T28 adapter outcome. :unknown can mean an effect committed before reply loss."
  [s {:keys [op i outcome committed?] :or {committed? false}}]
  (let [rec (record s op) k (:cap rec)
        st (get-in rec [:steps i]) effect [op (:id st)]]
    (current-cap! s k #{:settling})
    (require! (and st (every? #(= :done (:status %)) (take i (:steps rec)))
                   (#{:pending :unknown :failed} (:status st))
                   (not (:permanent? st))) ::step-not-ready {:op op :i i :step st})
    (let [effect? (or (= :ok outcome) (and (= :unknown outcome) committed?))
          duplicate? (contains? (:adapter-effects s) effect)
          s (cond-> s effect? (update :adapter-effects conj effect)
                    effect? (emit {:event :adapter-effect :effect effect :duplicate? duplicate?
                                   :logical-execution? (not duplicate?)}))]
      (-> s (assoc-in (into (record-path s op) [:steps i :status])
                      ({:ok :done :fail :failed :fail-permanent :failed :unknown :unknown} outcome))
          (assoc-in (into (record-path s op) [:steps i :permanent?]) (= outcome :fail-permanent))
          (assoc-in (into (record-path s op) [:steps i :witness]) (when (= :ok outcome) [:witness effect]))
          (cond-> (not= :ok outcome) (assoc-in (into (cap-path s k) [:disposition]) :incomplete))))))

(defn t29-finish
  "T29 sole merged/discarded transition and staged effect release."
  [s {:keys [op]}]
  (let [rec (record s op) k (:cap rec)
        cap (cap s k) w (:world cap)]
    (require! (and rec (#{:merge :discard} (:kind rec)) (every? #(= :done (:status %)) (:steps rec))) ::unfinished {:op op})
    (let [s (-> s (put-cap k (assoc cap :disposition (if (= :merge (:kind rec)) :merged :discarded)))
                (assoc-in (into (record-path s op) [:effects-released?]) true)
                (cond-> (= :cleanup (first (:holder cap)))
                  (update-in [:custody :claims] dissoc (second (:holder cap)))))
          needed (set (concat
                       (mapcat (fn [[_ r]] (when-not (:effects-released? r) (vals (:bases r))))
                               (all-records s))
                       (mapcat (fn [[_ cap]] (when-not (terminal (:disposition cap)) (vals (:bases cap))))
                               (all-caps s))))
          freed (remove needed (concat (vals (:bases rec)) (vals (:bases cap))))
          s (update s :freed-bases into freed)]
      (if (and (wr s w) (every? #(terminal (:disposition (val %))) (caps-of s w)))
        (t34-release-world s {:w w}) s))))

(defn t30-recover
  "T30 forward recovery; permanent failures remain incomplete."
  [s {:keys [op k payload caller]}]
  (let [rec (record s op) cap (cap s k)]
    (require! rec ::missing-record {:op op})
    (require! (= payload (:payload-hash rec)) ::changed-payload {:op op})
    (authenticate-holder! s k caller)
    (require! (= k (:cap rec)) ::stale-capability {:k k})
    (if (terminal (:disposition cap)) s
        (do (current-cap! s k #{:settling :incomplete})
            (assoc-in s (into (cap-path s k) [:disposition])
                      (if (some :permanent? (:steps rec)) :incomplete :settling))))))

(defn process-loss-state? [s]
  (and (false? (:process-live? s)) (false? (:restarted? s))
       (every? empty? [(:worlds s) (:cuts s) (:registry s) (:caps s) (:records s)
                       (get-in s [:custody :by-holder]) (get-in s [:custody :claims])])
       (= {:handles {} :threads {} :native {} :waiters {} :gc [] :outside [] :principals #{}}
          (:env s))))

(defn t31-crash
  "Process loss destroys volatile actors; restart freshly owns every durable leaf."
  [s {:keys [phase] :or {phase :crash}}]
  (require! (#{:crash :restart} phase) ::invalid-crash-phase {:phase phase})
  (when (= phase :restart)
    (require! (process-loss-state? s) ::not-crashed {:phase phase}))
  (if (= phase :restart)
    (let [s (-> s (assoc :restarted? true :process-live? true) (update :recovery-epoch inc)
                (assoc :custody {:by-holder {} :claims {}}))
          holder [:recovery :durable (:recovery-epoch s)]]
      (reduce
       (fn [state [k c]]
         (if (terminal (:disposition c)) state
             (let [c (assoc c :holder holder :holder-acquisition nil)
                   state (put-cap state k c)]
               (if (and (= :open (:disposition c)) (nil? (record state (:op c))))
                 (let [op (fresh-recovery-operation state k)
                       steps (mapv (fn [i sys] {:id i :kind :system-discard :system sys
                                                :recovery :retry :status :pending :witness nil :effect-id [op i]})
                                   (range) (sort (set/intersection (:scope c) (get-in state [:model :durable-systems]))))]
                   (-> state (put-cap k (assoc c :disposition :settling :op op :kind :discard))
                       (assoc-in [:durable :records op] {:op op :cap k :kind :discard :payload-hash :recovery
                                                         :steps steps :bases (:bases c) :effects-released? false})))
                 state))))
       (update-in s [:durable :records]
                  (fn [records]
                    (into {} (for [[op rec] records]
                               [op (if (:successors rec)
                                     (update rec :successors
                                             #(mapv (fn [desc]
                                                      (if (and (not (:durable? desc)) (nil? (cap s (:k desc))))
                                                        (assoc desc :disposition :discarded :vanished? true) desc)) %)) rec)]))))
       (get-in s [:durable :caps])))
    (-> s (assoc :worlds {} :cuts {} :registry #{} :caps {} :records {} :restarted? false
                 :custody {:by-holder {} :claims {}} :process-live? false)
        (update-in [:durable :records]
                   (fn [records]
                     (into {} (for [[op rec] records]
                                [op (if (:successors rec)
                                      (update rec :successors
                                              #(mapv (fn [desc] (if (:durable? desc) desc
                                                                    (assoc desc :disposition :discarded :vanished? true))) %)) rec)]))))
        (assoc :env {:handles {} :threads {} :native {} :waiters {} :gc [] :outside [] :principals #{}}))))

(defn consumption-record [s k op kind payload]
  (let [c (cap s k)]
    (fresh-operation! s op)
    (assoc-in s (if (:durable? c) [:durable :records op] [:records op])
              {:op op :cap k :kind kind :payload-hash payload :steps [] :bases {} :effects-released? true})))

(defn t32-transfer
  "T32 affine capability transfer, retaining operation identity."
  [s {:keys [k successor holder op caller acceptor acceptance]}]
  (let [cap (current-cap! s k #{:open})]
    (require! (:published? cap) ::unpublished-capability {:k k})
    (require! (wr s (:world cap)) ::missing-world {:world (:world cap)})
    (authenticate-holder! s k caller)
    (require! (#{:execution-owner :external} (first caller)) ::claimed-capability {:k k})
    (require! (= holder acceptor) ::unaccepted-transfer {:holder holder :acceptor acceptor})
    (fresh-cap! s successor)
    (let [acquisition (accept-holder! s holder acceptance)]
      (-> s (consumption-record k op :transfer {:successor successor :holder holder})
          (put-cap k (assoc cap :disposition :transferred :op op :successors [successor]))
          (put-cap successor (assoc cap :holder holder :holder-acquisition acquisition
                                    :pred k :op nil :successors []))))))

(defn t33-partition
  "T33 partition into disjoint scopes exactly covering the input."
  [s {:keys [k successors op caller]}]
  (let [cap (current-cap! s k #{:open}) scopes (map :scope successors)]
    (require! (:published? cap) ::unpublished-capability {:k k})
    (require! (wr s (:world cap)) ::missing-world {:world (:world cap)})
    (authenticate-holder! s k caller)
    (require! (#{:execution-owner :external} (first caller)) ::claimed-capability {:k k})
    (require! (and (seq successors) (= (count successors) (count (set (map :k successors))))
                   (every? (comp seq :scope) successors)) ::invalid-partition {:successors successors})
    (doseq [desc successors] (fresh-cap! s (:k desc)))
    (require! (and (= (:scope cap) (apply set/union #{} scopes))
                   (= (reduce + (map count scopes)) (count (:scope cap))))
              ::invalid-partition {:scopes scopes})
    (let [s (consumption-record s k op :partition successors)
          s (-> s (assoc-in (conj (record-path s op) :successors)
                            (mapv (fn [desc] (assoc desc :holder (:holder cap)
                                                    :durable? (durable-scope? s (:scope desc)))) successors))
                (put-cap k (assoc cap :disposition :partitioned :op op :successors (mapv :k successors))))]
      (reduce (fn [state desc]
                (put-cap state (:k desc) (assoc cap :scope (:scope desc) :pred k
                                                :bases (select-keys (:bases cap) (:scope desc))
                                                :op nil :successors []))) s successors))))

(defn t34-release-world
  "T34 local teardown and publication of a lineage-only tombstone."
  [s {:keys [w]}]
  (let [world (wr s w) caps (caps-of s w)]
    (if (or (nil? world) (= :released (:status world))) s
        (do
          (require! (not-any? #(#{:settling :incomplete} (:disposition (val %))) caps)
                    ::settlement-open {:w w})
          (require! (or (nil? (get-in world [:lineage :parent]))
                        (every? #(terminal (:disposition (val %))) caps)) ::capability-open {:w w})
          (let [s (cleanup/retain-subtree s w (:root world)
                                          (into {} (for [[r _] (:runs world)] [r (owner-chain s w r)])))
                s (if *release-cancellation*
                    (update-in s [:env :native]
                               #(into {} (for [[id row] %]
                                           [id (if (and (= w (first (:owner row))) (cleanup/exit? row)
                                                        (not (contains? row :cancel-value)))
                                                 (assoc row :cancel-value (:value *release-cancellation*)) row)]))) s)
                s (reduce (fn [s [c cut]]
                            (if (and (active-cuts (:phase cut))
                                     (contains? (get-in cut [:participants :worlds]) w))
                              (t25-cut-fail s {:c c}) s)) s (:cuts s))
              ;; Release host creditors before the cascade can cancel them.
                s (reduce (fn [s [o ob]]
                            (if (= :host (first (:creditor ob)))
                              (let [[_ dw e] (:debtor ob)]
                                (if (cleanup/mailbox-control s dw e e)
                                  (-> (queue-mailbox-rejection s dw e o
                                                               (if *release-cancellation* (:value *release-cancellation*)
                                                                   :org.replikativ.spindel.engine.protocols/released))
                                      (end-obligation w o :creditor-cancelled))
                                  (-> s (end-obligation w o :creditor-cancelled)
                                      (emit {:event :host-delivery :world w :o o :value (if *release-cancellation* (:value *release-cancellation*) ::released)})))) s))
                          s (:obligations world))
              ;; Drop dormant copies without rejecting into any other copy.
                s (reduce (fn [s [r rr]]
                            (if (= :inherited (:status rr))
                              (-> s (end-run-links w r :cancelled)
                                  (update-in [:worlds w :runs] dissoc r)) s))
                          s (:runs world))
                s (close-owned s w (:root world))
                s (reduce (fn [s [v o]] (enqueue s v {:cancelled o}))
                          s (for [[v vw] (:worlds s) :when (not= w v)
                                  [o ob] (:obligations vw)
                                  :when (and (= [:entity w] (subvec (:debtor ob) 0 2))
                                             (known-foreign-obligation? s w v o ob))] [v o]))
                s (reduce (fn [s [o ob]]
                            (cond-> (end-obligation s w o :creditor-cancelled)
                              (= :host (first (:creditor ob)))
                              (emit {:event :host-delivery :world w :o o :value (if *release-cancellation* (:value *release-cancellation*) ::released)})))
                          s (:obligations (wr s w)))
                s (reduce (fn [s ev]
                            (cond (:start-for ev) (enqueue s (:creditor-world ev) {:cancelled (:o ev) :value (if *release-cancellation* (:value *release-cancellation*) ::released)})
                                  (:register-host ev) (emit s {:event :host-delivery :world w
                                                               :o (:register-host ev) :value (if *release-cancellation* (:value *release-cancellation*) ::released)})
                                  :else s)) s (:queue (wr s w)))
                parent (get-in world [:lineage :parent])
                s (if (and parent (ent s parent [:fork w]))
                    (enqueue s parent {:fork-released w}) s)
                ;; The world becomes a value-only tombstone. Physical
                ;; participants retain just the ancestry needed for joins.
                s (update-in s [:env :threads]
                             #(into {} (for [[th thread] %]
                                         [th (cond-> thread
                                               (and (= w (:world thread)) (:run thread))
                                               (assoc :anchor (owner-chain s w (:run thread))))])))
                s (update-in s [:env :native]
                             #(into {} (for [[n native] %]
                                         [n (cond-> native
                                              ;; Raw receipts froze their ancestry at first
                                              ;; physical claim (or queued rejection). Their
                                              ;; ordinary owner row may already be gone.
                                              (and (= w (first (:owner native))) (not= :joined (:state native))
                                                   (not (cleanup/mailbox-callback? native)))
                                              (assoc :anchor (owner-chain s w (second (:owner native))))
                                              (and (= w (first (:owner native))) (cleanup/mailbox-callback? native))
                                              (assoc :retired? true))])))]
            (-> s
                ;; Run creation and enqueue share an order. Preserve its high
                ;; water mark before the value-only tombstone drops :seq.
                (assoc-in [:clocks w] (max (:seq (wr s w) 0) (get-in s [:clocks w] 0)))
                (assoc-in [:worlds w] (assoc (select-keys world [:id :lineage]) :status :released))
                (update :registry disj w)
                (update-in [:env :outside]
                           (fn [outside]
                             (let [attempt? #(and (= w (:w %)) (or (:deferred-assignment (:event %)) (:mailbox-post (:event %))))
                                   held (into (vec (remove #(and (= w (:w %)) (not (attempt? %))) outside))
                                              (for [event (:queue (wr s w)) :when (or (:deferred-assignment event) (:mailbox-post event))]
                                                {:w w :event event}))
                                   ordered (sort-by #(get-in % [:event :seq]) (filter attempt? held))]
                               ;; Replace only this world's attempt slots. Other
                               ;; worlds retain their relative positions/order.
                               (loop [remaining held attempts ordered result []]
                                 (if-let [next (first remaining)]
                                   (if (attempt? next)
                                     (recur (rest remaining) (rest attempts) (conj result (first attempts)))
                                     (recur (rest remaining) attempts (conj result next)))
                                   result)))))))))))

(defn- release-logical-profile? [s root required]
  (let [same-family? #(= root (get-in s [:lineages % :root]))
        logical? (fn [world o ob]
                   (let [[kind dw e] (:debtor ob)]
                     (or (not= :entity kind) (= world dw)
                         (and (= [:run world] (subvec (vec (:creditor ob)) 0 2))
                              (#{:track :await-once :await-reactive} (:kind ob))
                              (same-family? world) (same-family? dw)
                              (or (#{:signal :atom :spin} (:kind (ent s dw e)))
                                  (and (= :released (:status (wr s dw)))
                                       (cancelling? s world o ob)))))))
        involved? (fn [world ob] (or (contains? required world)
                                     (and (= :entity (first (:debtor ob)))
                                          (contains? required (second (:debtor ob))))))
        relevant (for [[world row] (:worlds s) [o ob] (:obligations row)
                       :when (involved? world ob)] [world o ob])
        endpoint-worlds (into required (mapcat (fn [[world _ ob]]
                                               (cons world (when (= :entity (first (:debtor ob)))
                                                             [(second (:debtor ob))]))) relevant))]
    (and
     (every? (fn [[world o ob]]
               (and (or (not= :entity (first (:creditor ob))) (= world (second (:creditor ob))))
                    (logical? world o ob))) relevant)
     (not-any? #(and (active-cuts (:phase %))
                     (seq (set/intersection endpoint-worlds (get-in % [:participants :worlds])))) (vals (:cuts s)))
     ;; Controls at an involved foreign endpoint are still outside this
     ;; bounded profile, even when that endpoint is outside cap/debt closure.
     (not-any? #(some % [:start-for :register-host])
               (mapcat (fn [world] (pending-events s world)) endpoint-worlds))
     (every? (fn [world]
               (let [row (wr s world)
                     supported-entity? #(#{:signal :atom :spin} (:kind (ent s world %)))
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
                              (pending-events s world))))) required))))

(defn- local-release-profile! [s w]
  (let [caps (all-caps s) root (get-in s [:lineages w :root])
        required (loop [pending [w] seen #{}]
                   (if-let [world (peek pending)]
                     (if (seen world) (recur (pop pending) seen)
                         (recur (into (pop pending)
                                      (concat (for [[_ c] caps
                                                    :when (and (not (terminal (:disposition c)))
                                                               (= :execution-owner (first (:holder c)))
                                                               (= world (second (:holder c))))] (:world c))
                                              (map :target-world (vals (get-in s [:env :cleanup-targets world])))))
                                (conj seen world))) seen))
        supported? (fn [c]
                     (or (terminal (:disposition c))
                         (and (empty? (:scope c))
                              (= root (get-in s [:lineages (:world c) :root]))
                              (or (= :open (:disposition c))
                                  (and (= :discard (:kind c)) (empty? (:steps (record s (:op c)))))))))]
    (require! (wr s w) ::unknown-world {:w w})
    (require!
     (and
      (every? supported? (for [[_ c] caps
                               :when (and (= :execution-owner (first (:holder c)))
                                          (contains? required (second (:holder c))))] c))
      (every? supported? (for [world required [_ debt] (get-in s [:env :cleanup-targets world])]
                           (cap s (:cap debt))))
      (every? (fn [world]
                (let [row (wr s world)]
                  (and row (= root (get-in s [:lineages world :root]))))) required)
      (release-logical-profile? s root required))
     ::unsupported-world-release {:w w})))

(defn release-request [s {:keys [w caller-th op callback] :as action}]
  (lifecycle/caller-worlds! s action)
  (require! (and (nil? op) (nil? callback)) ::cleanup-only {:action action})
  (when-let [thread (get-in s [:env :threads caller-th])]
    (when-let [r (:run thread)]
      (require! (and (nil? (:cleanup-ticket thread)) (not (:retired? thread))
                     (not= :unwinding (:status (run s (:world thread) r))))
                ::cleanup-only {:action action})))
  (when-not (get-in s [:env :releases w]) (local-release-profile! s w))
  (let [existing (get-in s [:env :releases w]) s (lifecycle/request s action)
        reason (get-in s [:env :releases w :reason])]
    (if existing s
        (binding [*release-cancellation* {:value reason}]
          (t34-release-world s {:w w})))))

(defn release-ready? [s w]
  (lifecycle/composed-ready? s w
                             (fn [state world]
                               (and (= :released (:status (wr state world)))
                                    (join-ready? state world world)))))

(defn admit-join-bundle [s w event]
  (let [v (:join-bundle event)]
    (reduce
     (fn [s [o {:keys [debtor source-world source-o]}]]
       (if-let [ob (get-in s [:worlds v :obligations o])]
         (let [source (get-in s [:worlds source-world :obligations source-o])
               source-admitted? (and source (= [:entity w debtor] (:debtor source))
                                     (or (contains? (:fdeps (wr s w)) [debtor source-world source-o])
                                         (some (fn [[tag target d]]
                                                 (and (= :bundle tag) (= source-world target) (contains? d debtor)))
                                               (:fdeps (wr s w)))))
               admitted? (or (contains? (:fdeps (wr s w)) [debtor v o])
                             (some (fn [[tag target d]] (and (= :bundle tag) (= v target) (contains? d debtor)))
                                   (:fdeps (wr s w))))]
           (cond
             (or admitted? (cancelling? s v o ob)) s
             (and (= :live (:status (wr s w))) (ent s w debtor) source-admitted?)
             (cond-> (add-fdep s v o)
               (:completed? (ent s w debtor))
               (enqueue v {:completion debtor :debtor-world w :value (:result (ent s w debtor))}))
             :else (enqueue s v {:cancelled o :value ::released}))) s))
     s (:members event))))

(defn t36-cleanup
  "T36 local cleanup; an event whose row has gone is a no-op."
  [s {:keys [w]}]
  (if (= :released (:status (wr s w))) s
      (let [ev (first (:queue (wr s w)))
            _ (require! ev ::empty-queue {:w w})
            s (update-in s [:worlds w :queue] #(vec (rest %)))
            s (cond
                (:join-bundle ev) (admit-join-bundle s w ev)
                (:fdep-ended ev) (update-in s [:worlds w :releasing] disj (:fdep-ended ev))
                (:cancelled ev) (let [o (:cancelled ev)]
                                  (-> s (t06-resume {:w w :o o :value (:value ev ::cancelled)})
                                      (end-obligation w o :cancel-delivered)))
                (:fork-released ev) (update-in s [:worlds w :entities] dissoc [:fork (:fork-released ev)])
                :else (refuse ::not-cleanup {:event ev}))]
        (rule-l s w))))

(defn t37-start-for
  "T37 debtor-world admission of a queued foreign cold await."
  [s {:keys [w]}]
  (let [{e :start-for v :creditor-world o :o tok :tok :as ev} (first (:queue (wr s w)))
        _ (require! e ::not-start-request {:event ev})
        _ (require! (not (#{:deferred :mailbox} (:kind (ent s w e)))) ::not-computation {:w w :e e})
        ob (get-in s [:worlds v :obligations o])
        pending? (and ob (= :armed (:slot ob))
                      (pending-start? s v o ob) (not (cancelling? s v o ob))
                      (not (contains? (:fdeps (wr s w)) [e v o]))
                      (not (some (fn [[tag target debtors]]
                                   (and (= :bundle tag) (= v target) (contains? debtors e)))
                                 (:fdeps (wr s w)))))
        s (update-in s [:worlds w :queue] #(vec (rest %)))]
    (cond
      (not pending?) s
      (not= :live (:status (wr s w))) (enqueue s v {:cancelled o :value ::released})
      :else
      (let [owner (:root (wr s w))
            s (if (ent s w e) s (assoc-in s [:worlds w :entities e] (spin-row s w e owner)))
            completed? (:completed? (ent s w e))
            s (if (or completed? (work? (run s w (current s w e)))) s
                  (first (start-run s w e owner :await)))
            s (-> s (touch w e tok) (add-fdep v o))]
        (if completed? (enqueue s v {:completion e :debtor-world w :value (:result (ent s w e))}) s)))))

(defn t35-host-entry
  "T35 H1; captured world cannot override an obligation's placement."
  [s {:keys [th op] :or {th :foreign}}]
  (require! (get-in s [:env :threads th :world]) ::no-world {:thread th})
  (if op (if (= :resume (:kind op))
           (if (cut-participant? s (:w op))
             (enqueue s (:w op) {:action (assoc op :t :t06)})
             (t06-resume s op)) s) s))

(defn finish-unwinding [s w r]
  (if (and (= :unwinding (:status (run s w r))) (not (physical? s w r)))
    (rule-l (update-in s [:worlds w :runs] dissoc r) w) s))

(defn slice-enter [s {:keys [w r th]}]
  (require! (not-any? (fn [[_ ob]]
                        (and (= [:run w r] (:creditor ob))
                             (let [[_ dw e] (:debtor ob)] (cleanup/mailbox-control s dw e e))))
                      (:obligations (wr s w))) ::mailbox-claim-required {:w w :r r})
  (require! (= :running (:status (run s w r))) ::not-running {:w w :r r})
  (require! (nil? (get-in s [:env :threads th :run])) ::thread-busy {:th th})
  (require! (not-any? #(and (= w (:world %)) (= r (:run %)))
                      (vals (get-in s [:env :threads]))) ::slice-busy {:w w :r r})
  (assoc-in (cond-> s (get-in s [:model :cps-exit?])
                    (assoc-in [:worlds w :runs r :cps-entered?] true))
            [:env :threads th]
            (merge (get-in s [:env :threads th])
                   {:world w :scope r :run r :obligation-world w :executing? true})))

(defn t38-slice-exit [s {:keys [th]}]
  (let [{:keys [world run] :as thread} (get-in s [:env :threads th])]
    (require! run ::no-slice {:th th})
    (require! (not-any? #(and (cleanup/timer-resource? %) (= [world run] (:owner %))
                              (= th (:installer %)) (= :pending (:install %)))
                        (vals (get-in s [:env :native])))
              ::timer-install-pending {:th th})
    (-> (cleanup/slice-exit s thread)
        (update-in [:env :threads th]
                   #(-> % (assoc :run nil :scope nil :executing? false)
                        (dissoc :retired? :obligation-world :anchor :cleanup-ticket)))
        (finish-unwinding world run))))

(defn join-observation [s {:keys [w x timeout?]}]
  (let [runs (join-blockers s w x) ready? (join-ready? s w x)]
    (when (and (not ready?) timeout?)
      (refuse ::join-timeout {:w w :x x :busy runs}))
    {:complete? ready? :busy runs}))

(defn finalization-wait [s {:keys [th] :as action}]
  (let [{:keys [world run]} (get-in s [:env :threads th])]
    (cleanup/begin-finalization s (assoc action :anchor (owner-chain s world run)
                                         :current? (= run (current s world (first run)))))))

(defn finalization-resume [s {:keys [n] :as action}]
  (let [[w r] (get-in s [:env :native n :owner])]
    (cleanup/resume-finalization s (assoc action :current? (= r (current s w (first r)))))))

(def transitions
  {:t01 t01-create-spin :t02 t02-create-signal :t03 t03-touch-keyed :t04 t04-invoke
   :timer-register timer-register :timer-install-result timer-install-result
   :timer-fire timer-fire :timer-return timer-return :timer-handle-release timer-handle-release
   :t05 t05-park :t06 t06-resume :t07 t07-complete :t08 t08-deliver :t09 t09-reenter
   :t10 t10-supersede :t11 t11-cancel :t12 t12-open-scope :t13 t13-close-scope
   :t14 t14-pin :t15 t15-cancel-world-work :t16 t16-handle-unreachable :t17 t17-gc-notify
   :t18 t18-release-idle-caches :t19 t19-fork-following :t20 t20-cut-fence :t20q t20q-cut-fence
   :t21 t21-cut-drain :t22 t22-cut-capture :t23 t23-cut-attach :t24 t24-cut-release
   :t25 t25-cut-fail :t26 t26-seal :t27 t27-prepare :t28 t28-settlement-step
   :t29 t29-finish :t30 t30-recover :t31 t31-crash :t32 t32-transfer
   :t33 t33-partition :t34 t34-release-world :t35 t35-host-entry :t36 t36-cleanup :t37 t37-start-for :t38 t38-slice-exit :slice-enter slice-enter
   :finalization-wait finalization-wait :finalization-resume finalization-resume
   :cleanup-adopt cleanup/adopt :cleanup-claim cleanup/claim :cleanup-park cleanup/suspend
   :cleanup-deliver cleanup/deliver :cleanup-return cleanup/returning
   :cleanup-cell cleanup/access
   :operation-start cleanup/operation-start :operation-await operation-await
   :operation-deliver operation-deliver :operation-claim cleanup/operation-claim
   :operation-terminal cleanup/operation-terminal :operation-return cleanup/operation-return
   :release-request release-request :release-observe lifecycle/observe
   :release-detach lifecycle/detach :release-notify lifecycle/notify
   :source-unreachable managed-cells/unreachable :reap-source managed-cells/reap
   :invalidate-computation invalidate-computation :withdraw-deref withdraw-deref
   :cancel-computation cancel-computation :signal-publish publish-signal
   :deferred-create deferred-create :deferred-request deferred-request :deferred-assign deferred-assign
   :deferred-observe deferred-observe :deferred-protect deferred-protect
   :mailbox-create mailbox-create :mailbox-post-request mailbox-post-request :mailbox-post mailbox-post
   :mailbox-take mailbox-take :mailbox-take-now mailbox-take-now :mailbox-claim mailbox-claim
   :mailbox-return mailbox-return :mailbox-detach mailbox-detach})

(defn changed-worlds [before after]
  (set (for [w (set/union (set (keys (:worlds before))) (set (keys (:worlds after))))
             :when (not= (wr before w) (wr after w))] w)))

(defn release-fixpoint
  "Only the acting world's rule-L fixpoint. Foreign cleanup is a T36 event."
  [before after w]
  (if (and w (wr after w) (not= :released (:status (wr after w)))) (rule-l after w) after))

(defn acting-world [s a]
  (or (when (and (not (#{:slice-enter :t35} (:t a)))
                 (get-in s [:env :threads (:th a) :run]))
        (get-in s [:env :threads (:th a) :world]))
      (:w a) (first (get-in s [:env :native (:n a) :owner])) (get-in a [:op :w])
      (when (#{:t38 :slice-enter :native-progress} (:t a))
        (or (get-in s [:env :threads (:th a) :world])
            (first (get-in s [:env :native (:n a) :owner]))))
      (when (#{:t01 :t02 :t04} (:t a))
        (get-in s [:env :threads (get a :th :host) :world]))
      (:world (cap s (:k a))) (:world (cap s (:cap (record s (:op a)))))
      (first (get-in s [:cuts (:c a) :participants :worlds]))
      (first (get-in a [:participants :worlds]))))

(defn budget-key [a]
  (case (:t a)
    :t31 (when (not= :restart (:phase a)) [:crash])
    :t28 (when (not= :ok (:outcome a)) [(:outcome a) (:op a) (:i a)])
    :slice-enter [:slice-enter (:w a) (:r a)]
    :signal-write [:write (:w a) (:e a)]
    :t04 [:invoke (:w a) (:e a)]
    :t12 [:scope-open (:w a)]
    :t05 nil
    :timer-register [:timer-register (:w a) (:r a)]
    :mailbox-create [:mailbox-create (:w a) (:e a)]
    :mailbox-post-request [:mailbox-post (:w a) (:e a)]
    :mailbox-take [:mailbox-take (:w a) (:e a)]
    :mailbox-take-now [:mailbox-now (:w a) (:e a)]
    :t02 [:source (:w a) (:kind a :signal) (or (:key a) (:e a))]
    :t14 (when (:pin? a) [:pin (:w a) (:e a)])
    :t09 [:reenter (:w a) (:e a)]
    nil))

(defn- step*
  "One atomic transition. Refusal throws ex-info; its :state is the unchanged input.
  Native progress, arrivals and thread re-entry are explicit environment actions.
  An explicit :th attributes a requested effect to that thread's slice; omitted
  :th denotes an engine/coordinator action (legacy host selection still applies)."
  [s {:keys [t] :as a}]
  (try
    (require! (boolean? (:process-live? s)) ::invalid-process-state {:process-live? (:process-live? s)})
    (require! (or (:process-live? s) (= :t31 t)) ::process-lost {:action a})
    (let [thread (get-in s [:env :threads (:th a)])
          slice? (:run thread)
          unwinding? (= :unwinding (:status (run s (:world thread) (:run thread))))
          a (if (and slice? (not (#{:t38 :slice-enter :t35} t))) (assoc a :w (:world thread)) a)
          w (acting-world s a)
          _ (when (and slice? (not (#{:t38 :cleanup-adopt :cleanup-park :cleanup-return :cleanup-cell :deferred-request :mailbox-post-request :mailbox-take-now :mailbox-claim :mailbox-return :operation-start :operation-await :operation-deliver :operation-claim :operation-terminal :operation-return} t)) (= :released (:status (wr s (:world thread)))))
              (refuse ::released {:w w :thread (:th a)}))
          _ (when (and unwinding?
                       (#{:t01 :t02 :t03 :t04 :t05 :t12 :t19 :t20 :t20q
                          :invalidate-computation :withdraw-deref :cancel-computation :signal-publish :deferred-create :deferred-observe :mailbox-create :mailbox-take :timer-register} t))
              (refuse ::cancelled {:w w :r (:run thread)}))
          _ (when (and (or (:cleanup-ticket thread)
                           (cleanup/exit? (get-in s [:env :native (cleanup/ticket (:world thread) (:run thread))])))
                       (not (#{:t38 :cleanup-adopt :cleanup-park :cleanup-return :cleanup-cell :deferred-request :mailbox-post-request :mailbox-take-now :mailbox-claim :mailbox-return :operation-start :operation-await :operation-deliver :operation-claim :operation-terminal :operation-return} t)))
              (refuse ::cleanup-only {:thread (:th a) :action a}))
          _ (when (and (cleanup/protected-operation-id? (:op a))
                       (not (#{:operation-start :operation-await :operation-deliver :operation-claim
                               :operation-terminal :operation-return :cleanup-cell :deferred-request :mailbox-post-request :mailbox-take-now :signal-write :release-observe :release-detach} t)))
              (refuse ::cleanup-only {:action a}))
          _ (when (:callback a)
              (let [receipt (get-in s [:env :native (:callback a)])]
                (require! (and (cleanup/mailbox-callback? receipt)
                               (or (= (:frame a) (:frame receipt))
                                   (and (= :mailbox-claim t) (= :queued (:phase receipt))
                                        (= (:frame a) [:mailbox-frame (:consumer receipt)])))
                               (= w (first (:owner receipt)))
                               (or (= :mailbox-claim t) (cleanup/mailbox-callback-entered? s receipt))
                               (#{:cleanup-cell :deferred-request :mailbox-post-request :mailbox-take-now :mailbox-take :mailbox-claim :mailbox-return :release-observe :release-detach} t))
                          ::cleanup-only {:action a})))
          _ (when (and (= :signal-write t) (:op a))
              (let [participant (cleanup/operation s (:op a))
                    ticket (get-in s [:env :native (first (:op a))])]
                (require! (and participant (cleanup/finalizing? ticket)
                               (= w (first (:owner ticket)))
                               (contains? (:frames participant) (:frame a))
                               (= (:parent participant) (current s w (first (:parent participant)))))
                          ::cleanup-only {:action a})))
          _ (let [resume (case t :t06 a :t35 (when (= :resume (get-in a [:op :kind])) (:op a)) nil)
                  ob (when resume (get-in s [:worlds (:w resume) :obligations (:o resume)]))
                  [_ dw e] (:debtor ob)]
              (when (:timer ob)
                (refuse ::unsupported-timer-resume {:action a}))
              (when (and ob (cleanup/mailbox-control s dw e e))
                (refuse ::unsupported-mailbox-resume {:action a})))
          _ (when (#{:t20 :t20q} t)
              (let [worlds (get-in a [:participants :worlds])]
                (when (some #(and (cleanup/timer-resource? %) (contains? worlds (first (:owner %))))
                            (vals (get-in s [:env :native])))
                  (refuse ::unsupported-timer-cut {:action a}))
                (when (some #(deferred-world? s % (wr s %)) worlds)
                  (refuse ::unsupported-resource-cut {:action a}))))
          before s s (assoc s :events [])]
      (when (and (quiescent-cut? s (acting-world s a))
                 (#{:t01 :t02 :t03 :t04 :t05 :t06 :t07 :t08 :t09 :t10 :t11
                    :t12 :t13 :t14 :t15 :t17 :t18 :t19 :unsubscribe :queued :t36 :t37
                    :invalidate-computation :withdraw-deref :cancel-computation :signal-publish :deferred-create :deferred-observe :mailbox-create :mailbox-take :timer-register} t))
        (refuse ::not-admitted {:action a}))
      (lifecycle/refresh
       (refresh-timer-anchors
        (release-fixpoint
         before
         (let [s (if-let [key (budget-key a)]
                   (update-in s [:uses key] (fnil inc 0)) s)]
           (case t
             :t02 (do (require! (not (#{:deferred :mailbox} (:kind a))) ::reserved-source-kind {:kind (:kind a)})
                      (t02-create-signal s a))
             :queued
             (let [w (:w a) ev (first (:queue (wr s w)))
                   _ (require! ev ::empty-queue {:w w})
                   s (update-in s [:worlds w :queue] #(vec (rest %)))]
               (cond (:mailbox-post ev)
                     (mailbox-post (update-in s [:worlds w :queue] #(into [ev] %))
                                   (assoc (dissoc ev :mailbox-post) :w w :e (:mailbox-post ev)))
                     (:deferred-assignment ev)
                     (deferred-assign (update-in s [:worlds w :queue] #(into [ev] %))
                                      (assoc (dissoc ev :deferred-assignment) :w w :e (:deferred-assignment ev)))
                     (:action ev) (step s (:action ev))
                     (some ev [:fdep-ended :cancelled :fork-released :join-bundle]) (t36-cleanup (update-in s [:worlds w :queue] #(into [ev] %)) {:w w})
                     (:start-for ev) (t37-start-for (update-in s [:worlds w :queue] #(into [ev] %)) {:w w})
                     (:register-host ev)
                     (let [e (:e ev) o (:register-host ev)]
                       (if (and (ent s w e) (= :live (:status (wr s w))))
                         (let [s (touch s w e (:tok ev))
                               cached? (and (:completed? (ent s w e))
                                            (not (work? (run s w (current s w e)))))
                               s (if cached? (emit s {:event :host-delivery :world w :o o}) s)]
                           (if (or (not cached?) (and (:standing? (:ob ev)) (not (final? s w e))))
                             (assoc-in s [:worlds w :obligations o] (:ob ev)) s))
                         (emit s {:event :host-delivery :world w :o o :value ::released})))
                     (:custody-dispatch ev)
                     (if-let [claim (get-in s [:custody :claims (:custody-dispatch ev)])]
                       (let [k (:cap ev) c (cap s k) holder [:cleanup (:custody-dispatch ev)]]
                         (require! (and (= k (:cap claim)) (= w (:target-world claim))
                                        (= (:op ev) (:settlement-op claim)) (= holder (:holder c)))
                                   ::invalid-custody-claim {:event ev})
                         (let [s (case (:disposition c)
                                   :open (t26-seal s {:k k :caller holder :op (:settlement-op claim) :kind (:kind claim)})
                                   :incomplete (t30-recover s {:k k :caller holder :op (:settlement-op claim)
                                                               :payload (:payload-hash (record s (:settlement-op claim)))})
                                   s)]
                           (assoc-in s [:custody :claims (:custody-dispatch ev) :phase] :active)))
                       (do (require! (terminal-custody-envelope? s w ev) ::invalid-custody-claim {:event ev}) s))
                     (:completion ev) (t08-deliver s (assoc ev :w w :e (:completion ev) :dequeued? true))
                     :else s))
             :native-progress
             (let [native (get-in s [:env :native (:n a)])
                   [w r] (:owner native)]
               (require! (not (or (cleanup/protected? native) (cleanup/mailbox-callback? native) (cleanup/timer-resource? native))) ::protected-cleanup {:n (:n a)})
               (-> s (update-in [:env :native (:n a)]
                                #(cond-> (merge % (select-keys a [:state :boundary?]))
                                   (= :joined (:state a)) (dissoc :anchor)))
                   (finish-unwinding w r)))
             :waiter-unregister (update-in s [:env :waiters] dissoc (:token a))
             :thread-entry
             (do (require! (nil? (get-in s [:env :threads (:th a) :run])) ::thread-busy {:th (:th a)})
                 (require! (and (nil? (get-in a [:thread :cleanup-ticket]))
                                (not (cleanup/protected?
                                      (get-in s [:env :native (cleanup/ticket (get-in a [:thread :world])
                                                                              (get-in a [:thread :run]))]))))
                           ::protected-cleanup {:th (:th a)})
                 (assoc-in s [:env :threads (:th a)] (:thread a)))
             :unsubscribe
             (let [ob (get-in s [:worlds (:w a) :obligations (:o a)])
                   [_ dw _] (:debtor ob)]
               (require! (or (nil? ob) (:standing? ob)) ::not-standing {:o (:o a)})
               (-> s (end-obligation (:w a) (:o a) :creditor-cancelled) (rule-l (:w a))))
             :signal-write
             (let [w (:w a) e (:e a) er (ent s w e)]
               (require! (not= :released (:status (wr s w))) ::released {:w w})
               (when-not (and unwinding? (nil? er))
                 (require! (and (#{:signal :atom} (:kind er)) (or (:owner er) unwinding?)) ::released {:w w :e e}))
               (if (and unwinding? (nil? er)) s
                   (if (= :fenced (:admission (wr s w)))
                     (update-in s [:env :outside] conj
                                {:w w :event (cond-> {:signal-write e :value (:value a)}
                                               (false? (:publish? a)) (assoc :publish? false))})
                     (let [s (assoc-in s [:worlds w :entities e :result] (:value a))]
                       (if (false? (:publish? a)) s
                           (reduce #(enqueue %1 %2 {:completion e :debtor-world w :value (:value a) :source-change? true})
                                   s (conj (fdep-targets (wr s w) e) w)))))))
             :arrival (cond (:mailbox-post (:event a))
                            (mailbox-post s (assoc (dissoc (:event a) :mailbox-post)
                                                   :w (:w a) :e (:mailbox-post (:event a))))
                            (:deferred-assignment (:event a))
                            (deferred-assign s (assoc (dissoc (:event a) :deferred-assignment)
                                                      :w (:w a) :e (:deferred-assignment (:event a))))
                            :else (enqueue s (:w a) (:event a)))
             (if-let [f (transitions t)] (f s a) (refuse ::unknown-transition {:action a}))))
         (acting-world before a))) release-ready?))
    (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) e
      (throw (ex-info (ex-message e) (assoc (ex-data e) :state s :action a))))))

(defn step
  "Apply a transition with optional checked fresh-run allocation evidence.
   A present empty vector forbids allocation; copies consume no evidence."
  [s a]
  (binding [*liveness-cache* (or *liveness-cache* (volatile! nil))
            *cache-gc-only?* (= :t17 (:t a))]
    (try
      (if (contains? a :fresh-runs)
        (do (require! (and (vector? (:fresh-runs a))
                           (every? #(and (vector? %) (= 3 (count %))) (:fresh-runs a)))
                      ::invalid-run-allocation {:action a})
            (binding [*fresh-runs* (volatile! (:fresh-runs a))]
              (let [result (step* s a)]
                (require! (empty? @*fresh-runs*) ::unused-run-allocation {:remaining @*fresh-runs*})
                result)))
        (step* s a))
      (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) e
        (throw (ex-info (ex-message e) (assoc (ex-data e) :state s :action a)))))))

(defn attempt [s a]
  (try (if (= :join (:t a))
         {:state s :observation (join-observation s a)}
         {:state (step s a)})
       (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) e
         {:state s :refusal (dissoc (ex-data e) :state)})))

(defn structural-key
  "Comparable, lossless normal form for the model's heterogeneous EDN values.
  Type tags prevent collisions (including keyword/string and map/set/vector)."
  [x]
  (cond
    (nil? x) [0]
    (boolean? x) [1 (if x 1 0)]
    (number? x) [2 #?(:clj (cond (integer? x) 0 (ratio? x) 1 (decimal? x) 2 :else 3)
                      :cljs 0) x]
    (keyword? x) [3 (or (namespace x) "") (name x)]
    (symbol? x) [4 (or (namespace x) "") (name x)]
    (string? x) [5 x]
    (map? x) [6 (vec (sort (map (fn [[k v]] [(structural-key k) (structural-key v)]) x)))]
    (set? x) [7 (vec (sort (map structural-key x)))]
    (sequential? x) [8 (mapv structural-key x)]
    #?(:clj (char? x) :cljs false) [9 #?(:clj (int x) :cljs x)]
    :else (refuse ::non-model-value {:value x})))

(defn structural-order
  "Decorate once, compare structural values, then discard the decoration."
  [xs]
  (if (next xs)
    (map second (sort-by first (map (fn [x] [(structural-key x) x]) xs)))
    xs))

(defn canonical
  "Fixed map/set traversal, first-occurrence alpha-renaming, queue clock ranks.
  Structural entity ids and run generations are semantic. Audit events are
  checked on edges then removed. Resume/host monitors and budgets remain in key."
  [s]
  (let [renames (atom {}) counters (atom {})
        tags #{:w :o :tok :op :cap :cut}
        id? #(and (vector? %) (= 2 (count %)) (tags (first %)))
        ;; Previously assigned names must sort before unvisited ids. In
        ;; particular, :caps can encounter a child world before its parent.
        ;; Re-sort composite keys after each visit: a row's value may assign
        ;; names used by a remaining key. This makes first occurrence stable.
        order-key (fn order-key [x]
                    (cond
                      (id? x) [10 (structural-key (first x))
                               (if-let [id (get @renames x)]
                                 [0 (second id)] [1 (structural-key (second x))])]
                      (map? x) [6 (vec (sort (map (fn [[k v]] [(order-key k) (order-key v)]) x)))]
                      (set? x) [7 (vec (sort (map order-key x)))]
                      (sequential? x) [8 (mapv order-key x)]
                      :else (structural-key x)))
        next-key (fn [xs]
                   (reduce (fn [a b] (if (pos? (compare (order-key a) (order-key b))) b a)) xs))
        rename (fn rename [x]
                 (if (id? x)
                   (or (get @renames x)
                       (let [tag (first x) id [tag (get @counters tag 0)]]
                         (swap! counters update tag (fnil inc 0))
                         (swap! renames assoc x id) id))
                   (cond
                     (map? x)
                     (if (not-any? coll? (keys x))
                       (into {} (for [k (structural-order (keys x))] [(rename k) (rename (get x k))]))
                       (loop [remaining (set (keys x)) result {}]
                         (if (empty? remaining) result
                             (let [k (next-key remaining)]
                               (recur (disj remaining k) (assoc result (rename k) (rename (get x k))))))))
                     (set? x)
                     (loop [remaining x result #{}]
                       (if (empty? remaining) result
                           (let [v (next-key remaining)]
                             (recur (disj remaining v) (conj result (rename v))))))
                     (coll? x) (mapv rename x)
                     :else x)))
        clocks (sort (set (keep identity
                                (concat (vals (:clocks s)) (map :seq (mapcat (comp vals :runs val) (:worlds s)))
                                        (map :seq (mapcat (comp :queue val) (:worlds s)))
                                        (map :seq (vals (:worlds s)))
                                        (map :seal-seq (vals (:worlds s)))
                                        (mapcat (comp vals :fence-seq val) (:cuts s))))))
        ranks (zipmap clocks (range))
        normalize (fn [world]
                    (cond-> (-> world
                                (update :runs #(into {} (for [[r rr] %] [r (update rr :seq ranks)])))
                                (update :queue #(mapv (fn [ev] (cond-> ev (:seq ev) (update :seq ranks))) %)))
                      (:seq world) (update :seq ranks)
                      (:seal-seq world) (update :seal-seq ranks)))
        done-effects (set (for [[op rec] (all-records s) st (:steps rec) :when (= :done (:status st))]
                            [op (:id st)]))
        s (-> s
              (update :uses #(into {} (remove (fn [[[kind op i] _]]
                                                (and (#{:fail :fail-permanent :unknown} kind)
                                                     (contains? done-effects [op i]))) %)))
              (update :adapter-effects #(set/difference % done-effects)))
        s (-> s (dissoc :events :serial)
              (update :clocks #(into {} (for [[w n] %] [w (ranks n)])))
              (update :worlds #(into {} (for [[w world] %] [w (normalize world)])))
              (update :cuts #(into {} (for [[c cut] %]
                                        [c (update cut :fence-seq (fn [fs] (into {} (for [[w n] fs] [w (ranks n)]))))]))))]
    (rename s)))

(defn non-idle-projection
  "TL4 observable engine projection (host reachability and GC queues excluded)."
  [s]
  (into {} (for [[w world] (:worlds s)]
             [w (-> (select-keys world [:status :admission :scopes :runs :obligations :fdeps :releasing :pins :queue])
                    (update :queue #(vec (remove (fn [ev]
                                                   (and (:completion ev)
                                                        (idle? s (get ev :debtor-world w) (:completion ev)))) %)))
                    (assoc :entities (into {} (for [[e er] (:entities world)
                                                    :when (not (idle? s w e))]
                                                [e (dissoc er :tokens)]))))])))

(defn timer-enabled
  "Opt-in finite timer alphabet: bounded registrations per exact ordinary run,
   one callback frame per registration, two handle outcomes and two variants.
   Ordinary lifetime/adoption actions remain supplied by the surrounding model."
  [s]
  (when (get-in s [:model :timers?])
    (concat
     (for [[th thread] (get-in s [:env :threads])
           :let [w (:world thread) r (:run thread) rr (run s w r) o (fresh s :o)]
           :when (and r (:executing? thread) (= :running (:status rr))
                      (= r (current s w (first r))) (nil? (:cleanup-ticket thread))
                      (< (get-in s [:uses [:timer-register w r]] 0) (get-in s [:model :registrations] 1)))]
       {:t :timer-register :w w :r r :th th :o o :n [:timer w o] :order 0 :delay-ms 1 :value :timer-value})
     (mapcat
      (fn [[n row]]
        (when (cleanup/timer-resource? row)
          (let [w (first (:owner row)) base {:w w :n n} frame [:timer-frame n 0]]
            (concat
             (when (= :pending (:install row))
               [(assoc base :t :timer-install-result :variant :ok :handle? true)
                (assoc base :t :timer-install-result :variant :ok :handle? false)
                (assoc base :t :timer-install-result :variant :error :handle? false :value :install-error)])
             (when (= :armed (:phase row))
               [(assoc base :t :timer-fire :frame frame :variant :ok :value (:value row))
                (assoc base :t :timer-fire :frame frame :variant :error :value :submission-error)])
             (when (contains? (:frames row) frame) [(assoc base :t :timer-return :frame frame)])
             (case (:handle row)
               :release-pending [(assoc base :t :timer-handle-release :phase :claim)]
               :release-claimed [(assoc base :t :timer-handle-release :phase :returned :variant :ok)
                                 (assoc base :t :timer-handle-release :phase :returned :variant :error :value :release-error)]
               [])))))
      (get-in s [:env :native])))))

(defn mailbox-enabled
  "Opt-in bounded Mailbox resource alphabet. Operation execution remains scripted."
  [s]
  (when (get-in s [:model :mailbox?])
    (let [cfg (:model s)]
      (concat
       (for [[w world] (:worlds s)
             :when (and (= :live (:status world)) (= :open (:admission world)))
             i (range (get cfg :mailboxes 1)) :let [e [:mailbox i]]
             :when (and (nil? (ent s w e)) (zero? (get-in s [:uses [:mailbox-create w e]] 0)))]
         {:t :mailbox-create :w w :e e :allocation e :scope (:root world)})
       (mapcat
        (fn [[w world]]
          (for [[e row] (:entities world) :when (and (= :mailbox (:kind row)) (:owner row))
                action (concat
                        (when (< (get-in s [:uses [:mailbox-post w e]] 0) (get cfg :mailbox-posts 2))
                          [{:t :mailbox-post-request :w w :e e :allocation e :value :message}])
                        (when (< (get-in s [:uses [:mailbox-take w e]] 0) (get cfg :mailbox-takes 2))
                          (let [o (fresh s :o)]
                            [{:t :mailbox-take :w w :e e :allocation e :kind :host :o o :order 0
                              :consumer [:host o] :available? (boolean (seq (get-in row [:mailbox :messages])))}]))
                        (when (< (get-in s [:uses [:mailbox-now w e]] 0) (get cfg :mailbox-now 2))
                          [{:t :mailbox-take-now :w w :e e :allocation e
                            :available? (boolean (seq (get-in row [:mailbox :messages])))}]))] action))
        (:worlds s))
       (for [[w world] (:worlds s) :let [event (first (:queue world))] :when (:mailbox-post event)]
         (assoc (dissoc event :mailbox-post) :t :mailbox-post :w w :e (:mailbox-post event)))
       (for [[[w e allocation] control]
             (let [ids (set (concat (for [[w world] (:worlds s) [e row] (:entities world)
                                          :when (= :mailbox (:kind row))] [w e (:allocation row)])
                                    (for [[key row] (get-in s [:env :cleanup-cells]) :when (= :mailbox (:kind row))]
                                      [(first key) (nth key 2) (:allocation row)])))]
               (for [[w e allocation :as id] ids] [id (cleanup/mailbox-control s w e allocation)]))
             [consumer reservation] (:reservations control)
             :when (and (= :host (:kind reservation)) (#{:reserved :claimed} (:state reservation)))]
         {:t :mailbox-claim :w w :e e :allocation allocation :consumer consumer
          :message-id (:message-id reservation) :frame [:mailbox-frame consumer]
          :inline? (= :claimed (:state reservation))})
       (for [[receipt row] (get-in s [:env :native]) :when (cleanup/mailbox-callback? row)
             :let [[w _] (:owner row) e (:allocation row) consumer (:consumer row)]]
         (if (= :queued (:phase row))
           {:t :mailbox-claim :w w :e e :allocation e :consumer consumer :variant :error
            :callback receipt :frame [:mailbox-frame consumer]}
           {:t :mailbox-return :w w :e e :allocation e :consumer consumer :frame (:frame row)}))))))

(defn raw-enabled
  "Concrete finite action alphabet. Bounds constrain allocation, not transition
  semantics. Includes refused operations, late callbacks, and all environment choices.
  Search profiles may supply an explicit alphabet; see bfs-check for coverage limits."
  [s]
  (let [cfg (:model s) worlds (:worlds s)
        next-w [:w (inc (reduce max -1 (map second (:known-worlds s))))]
        next-k [:cap next-w] next-c [:cut (count (:cuts s))]]
    (distinct
     (concat
      [{:t :t31 :phase :crash} {:t :t31 :phase :restart} {:t :t35 :th :foreign}]
      (when (:slices? cfg)
        (concat
         (for [[w world] worlds [r rr] (:runs world) th [:host :foreign]
               :when (and (= :running (:status rr))
                          (nil? (get-in s [:env :threads th :run]))
                          (not-any? #(and (= w (:world %)) (= r (:run %)))
                                    (vals (get-in s [:env :threads]))))]
           {:t :slice-enter :th th :w w :r r})
         (for [[th tr] (get-in s [:env :threads]) :when (:run tr)] {:t :t38 :th th})
         (for [[w world] worlds x (distinct (concat [w] (keys (:scopes world))
                                                    (keys (:runs world)) (mapcat :anchor (vals (:runs world)))
                                                    (mapcat (fn [[_ thread]]
                                                              (when (and (= w (:world thread)) (:run thread))
                                                                (cons (:run thread) (:anchor thread))))
                                                            (get-in s [:env :threads]))
                                                    (mapcat (fn [[_ native]]
                                                              (when (and (= w (first (:owner native)))
                                                                         (not= :joined (:state native)))
                                                                (cons (second (:owner native)) (:anchor native))))
                                                            (get-in s [:env :native]))))
               timeout? [false true]]
           {:t :join :w w :x x :timeout? timeout?})))
      (for [w (conj (set (keys worlds)) nil)
            :when (nil? (get-in s [:env :threads :foreign :run]))]
        {:t :thread-entry :th :foreign
         :thread {:world w :scope nil :run nil :read-permits #{} :excl-permits []}})
      (for [[w world] worlds [o ob] (:obligations world)
            :when (= :run (first (:creditor ob)))]
        {:t :t35 :th :foreign :op {:kind :resume :w w :o o :th :foreign}})
      (for [[tok h] (get-in s [:env :handles]) :when (:reachable? h)] {:t :t16 :tok tok})
      (get-in s [:env :gc])
      (cleanup/enabled s)
      (mailbox-enabled s)
      (timer-enabled s)
      (for [[n nr] (get-in s [:env :native]) :when (and (not= :joined (:state nr)) (not (or (cleanup/protected? nr) (cleanup/mailbox-callback? nr) (cleanup/timer-resource? nr))))]
        {:t :native-progress :n n :state :joined})
      (for [[n nr] (get-in s [:env :native])
            :when (and (not= :joined (:state nr)) (not (:boundary? nr)) (not (or (cleanup/protected? nr) (cleanup/mailbox-callback? nr) (cleanup/timer-resource? nr))))]
        {:t :native-progress :n n :state (:state nr) :boundary? true})
      (for [[token waiter] (get-in s [:env :waiters]) :when (:armed? waiter)]
        {:t :waiter-unregister :token token})
      (mapcat
       (fn [[w world]]
         (let [root (:root world) live (= :live (:status world))
               spins (filter #(= :spin (:kind (val %))) (:entities world))
               es (map key spins) local-runs (:runs world)]
           (concat
            [{:t :t15 :w w} {:t :t18 :w w} {:t :t34 :w w}]
            (when live
              (concat
               (for [i (range (:spins cfg)) :let [e [:spin i]]
                     mode (:invoke-modes cfg) f (:filters cfg)]
                 {:t :t04 :w w :e e :scope root :mode mode :filter {:mode f :origin w}})
               (when (and (< (:scope-balance world) (:scopes cfg))
                          (< (get-in s [:uses [:scope-open w]] 0) (:scope-births cfg)))
                 [{:t :t12 :w w :scope [:scope :id (:next-scope world)] :parent root}])
               (when (< (count (:known-worlds s)) (:world-ids cfg))
                 [{:t :t19 :w w :v next-w :k next-k :scope root}])
               (when (< (get s :cut-allocations 0) (:cuts cfg))
                 (for [t [:t20 :t20q]]
                   {:t t :c next-c :scope root
                    :participants {:worlds #{w} :components #{[w :sci-a] [w :sci-b]}
                                   :systems #{:a :b}}}))
               (when (and (pos? (:signals cfg)) (not-any? #(= :signal (:kind %)) (vals (:entities world))))
                 [{:t :t02 :w w :e [:signal 0] :key :k}])
               (when (and (pos? (:atoms cfg)) (not-any? #(= :atom (:kind %)) (vals (:entities world))))
                 [{:t :t02 :w w :e [:atom 0] :kind :atom}])
               (for [e es tok (range (:handles cfg))
                     :when (not (get-in s [:env :handles [:tok tok]]))]
                 {:t :t01 :w w :e e :tok [:tok tok]})))
            (for [[scope sr] (:scopes world) :when (= :open (:status sr))]
              {:t :t13 :w w :scope scope})
            (for [e es pin? [true false]] {:t :t14 :w w :e e :pin? pin?})
            (when live
              (for [e es [tok h] (get-in s [:env :handles])
                    :when (= e (:spin h))
                    mode (:invoke-modes cfg) f (:filters cfg)]
                {:t :t04 :w w :e e :scope root :tok tok :mode mode :filter {:mode f :origin w}}))
            (mapcat
             (fn [[r rr]]
               (concat
                [{:t :t11 :w w :r r} {:t :t07 :w w :r r}]
                (when (and live (= r (current s w (:spin rr))) (< (second r) (:generations cfg)))
                  (for [cause [:dirty :rerun! :track]] {:t :t09 :w w :e (:spin rr) :cause cause :order 0}))
                (when (= :running (:status rr))
                  (concat
                   [{:t :t05 :w w :r r :kind :timer :debtor [:host :executor]}
                    {:t :t05 :w w :r r :kind :external :debtor [:host :native]}
                    {:t :t03 :w w :r r :key :site}
                    {:t :t03 :w w :r r :key :key :kind :keyed-entry}]
                   (for [i (range (:spins cfg)) :when (not= [:spin i] (:spin rr))]
                     {:t :t01 :w w :r r :e [:spin i] :tok [:tok 0]})
                   (for [[dw dworld] worlds [e er] (:entities dworld)
                         kind (case (:kind er) :spin [:await-once :await-reactive]
                                    :signal [:track] :atom [:external] []) :when (not= e (:spin rr))]
                     {:t :t05 :w w :r r :kind kind :debtor [:entity dw e]}))))) local-runs)
            (for [[o _] (:obligations world)] {:t :t06 :w w :o o})
            (for [[o ob] (:obligations world) :when (:standing? ob)] {:t :unsubscribe :w w :o o})
            (for [[e er] (:entities world) :when (and live (#{:signal :atom} (:kind er)) (:owner er))]
              {:t :signal-write :w w :e e :value (not (:result er))})
            (when (seq (:queue world)) [{:t (if (some (first (:queue world)) [:fdep-ended :cancelled :fork-released :join-bundle]) :t36 (if (:start-for (first (:queue world))) :t37 :queued)) :w w}])))) worlds)
      (mapcat (fn [[c cut]]
                (concat [{:t :t25 :c c}]
                        (case (:phase cut)
                          :fenced [{:t :t21 :c c}]
                          :ready [{:t :t22 :c c}]
                          :captured (when (< (count (:known-worlds s)) (:world-ids cfg))
                                      (for [mode [:frozen :materialized]]
                                        {:t :t23 :c c :v next-w :k next-k :mode mode}))
                          :attached [{:t :t24 :c c :e [:spin (dec (:spins cfg))]}] []))) (:cuts s))
      (mapcat
       (fn [[k cap]]
         (let [op [:op k] w (:world cap) caller (some #{(:holder cap)} (custody-actors s))]
           (case (:disposition cap)
             :open (when (and caller (:published? cap) (not= :cleanup (first (:holder cap))))
                     (concat
                      [{:t :t26 :caller caller :k k :op op :kind :merge}
                       {:t :t26 :caller caller :k k :op op :kind :discard}
                       {:t :t26 :caller caller :k k :op op :kind :merge :force true}
                       {:t :t33 :k k :op op :caller caller :successors
                        (mapv (fn [sys] {:k [:cap k sys] :scope #{sys}}) (:scope cap))}]
                      (for [destination (custody-destinations s)]
                        (merge {:t :t32 :k k :successor [:cap k] :op op :caller caller} destination))))
             :sealed [{:t :t27 :k k :op (:op cap) :payload :payload :bases (:bases cap)
                       :steps (mapv (fn [i] {:id i :kind :stamp :system (first (sort (:scope cap))) :recovery :retry})
                                    (range (:steps cfg)))}]
             []))) (all-caps s))
      (mapcat
       (fn [[op rec]]
         (let [k (:cap rec) disposition (:disposition (cap s k))
               caller (some #{(:holder (cap s k))} (custody-actors s))
               i (first (keep-indexed #(when (not= :done (:status %2)) %1) (:steps rec)))]
           (concat
            (when caller
              [{:t :t30 :caller caller :op op :k k :payload (:payload-hash rec)}
               {:t :t30 :caller caller :op op :k k :payload :wrong}
               {:t :t30 :caller caller :op op :k :stale :payload (:payload-hash rec)}])
            (when (and (= :settling disposition) i)
              (for [[outcome committed?] [[:ok false] [:fail false] [:unknown false] [:unknown true] [:fail-permanent false]]]
                {:t :t28 :op op :i i :outcome outcome :committed? committed?}))
            (when (and (nil? i) (#{:merge :discard} (:kind rec))) [{:t :t29 :op op}])))) (all-records s))))))

(defn within-bounds?
  "State bounds apply to nested transitions too (notably T8 -> T9 and T24).
  Refused edges are stutters. This restricts the search, never step semantics."
  [s]
  (let [cfg (:model s)]
    (and (<= (count (:known-worlds s)) (:world-ids cfg))
         (<= (count (:registry s)) (:worlds cfg))
         (every? #(<= % (:generations cfg)) (vals (:generation-clock s)))
         (every? (fn [[[kind & _] n]]
                   (<= n (case kind :invoke (:invocations cfg) :host-register (:host-registrations cfg)
                               :register (:registrations cfg) :slice-enter (:slice-enters cfg) :source 1 :pin 1 :write (:writes cfg)
                               :scope-open (:scope-births cfg) :crash (:crashes cfg) :reenter (dec (:generations cfg))
                               :unknown (:unknowns cfg) (:fail :fail-permanent) (:failures cfg) n))) (:uses s))
         (<= (count (get-in s [:env :threads])) (:threads cfg))
         (<= (count (get-in s [:env :handles])) (:handles cfg))
         (<= (get s :cut-allocations 0) (:cuts cfg))
         (every? #(<= (count (:steps %)) (:steps cfg)) (vals (all-records s)))
         (every? (fn [[_ world]]
                   (and (<= (count (filter #(= :spin (:kind %)) (vals (:entities world)))) (:spins cfg))
                        (<= (count (filter #(= :signal (:kind %)) (vals (:entities world)))) (:signals cfg))
                        (<= (count (filter #(= :atom (:kind %)) (vals (:entities world)))) (:atoms cfg))
                        (<= (count (:scopes world)) (inc (:scopes cfg))))) (:worlds s)))))

(defn enabled
  "Allocation/site budgets close host and program nondeterminism. These bounds
  constrain only the exploration alphabet, never the transition preconditions.
  One crash+restart, one failure and one uncertainty per step by default.
  :scope-births bounds total opens per world independently of :scopes live rows;
  neither exploration budget restricts literal transition semantics.
  Generated T32/T33 consume predecessor-free caps only; repeated successor
  chains are supported by step and checked separately by literal traces."
  [s]
  (let [spin-counts (into {} (for [[w world] (:worlds s)]
                               [w (count (filter #(= :spin (:kind %)) (vals (:entities world))))]))]
    (filter
     (fn [a]
       (let [t (:t a) key (if (= :t05 t) [:register (:w a) (:r a) (:kind a) (:debtor a)] (budget-key a))
             n (get-in s [:uses key] 0) cfg (:model s)]
         (and
          (or (true? (:process-live? s)) (= :t31 t))
          (case t
            :t31 (if (= :restart (:phase a))
                   (process-loss-state? s)
                   (< (get-in s [:uses [:crash]] 0) (:crashes cfg)))
            :t28 (case (:outcome a)
                   (:fail :fail-permanent) (< (+ (get-in s [:uses [:fail (:op a) (:i a)]] 0)
                                                 (get-in s [:uses [:fail-permanent (:op a) (:i a)]] 0)) (:failures cfg))
                   :unknown (< n (:unknowns cfg)) true)
            :slice-enter (< n (:slice-enters cfg))
            :signal-write (< n (:writes cfg))
            :t04 (and (< n (:invocations cfg))
                      (< (get-in s [:uses [:host-register (or (read-source s (:w a) (:e a)) (:w a)) (:e a)]] 0)
                         (:host-registrations cfg))
                      (or (< (get-in s [:generation-clock [(:w a) (:e a)]] 0) (:generations cfg))
                          (let [dw (read-source s (:w a) (:e a)) er (ent s dw (:e a))]
                            (or (work? (run s dw (current s dw (:e a))))
                                (and (:completed? er) (not (:dirty? er)))))))
            :t05 (and (< n (:registrations cfg))
                      (let [[dk dw e] (:debtor a)]
                        (or (not (and (= :entity dk) (#{:await-once :await-reactive} (:kind a))))
                            (current s dw e) (:completed? (ent s dw e))
                            (< (get-in s [:generation-clock [dw e]] 0) (:generations cfg)))))
            :t02 (< n 1)
            :t14 (or (not (:pin? a)) (< n 1))
            :t09 (and (< n (dec (:generations cfg)))
                      (< (get-in s [:generation-clock [(:w a) (:e a)]] 0) (:generations cfg)))
            (:t32 :t33) (nil? (:pred (cap s (:k a))))
            true)
        ;; Internal T8/T21 delivery may call T9; checking only direct T9 actions
        ;; would leave an unbounded reactive completion cycle in the alphabet.
          (case t
            (:t01 :t04)
            (or (ent s (:w a) (:e a))
                (< (get spin-counts (:w a) 0) (:spins cfg))
                (and (= :t04 t)
                     (let [dw (read-source s (:w a) (:e a))]
                       (or (work? (run s dw (current s dw (:e a))))
                           (:completed? (ent s dw (:e a)))))))
            (:thread-entry :slice-enter :t22 :t08 :queued :t21 :t24 :t36 :t19 :t23) (within-bounds? (:state (attempt s a)))
            true))))
     (raw-enabled s))))
