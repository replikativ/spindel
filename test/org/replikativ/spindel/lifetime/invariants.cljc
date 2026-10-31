(ns org.replikativ.spindel.lifetime.invariants
  "Independent full scans for §4.5 and finite-trace monitors for §4.6.
  Predicates return evidence vectors: empty means satisfied, never suppressed."
  (:refer-clojure :exclude [bound?])
  (:require [clojure.set :as set]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]))

(defn entities [s] (for [[w world] (:worlds s) [e er] (:entities world)] [w e er]))
(defn runs [s] (for [[w world] (:worlds s) [r rr] (:runs world)] [w r rr]))
(defn obligations [s] (for [[w world] (:worlds s) [o ob] (:obligations world)] [w o ob]))
(defn fdeps [s] (set (for [[w world] (:worlds s) [e v o] (:fdeps world) :when (not= e :bundle)] [w e v o])))
(defn bundles [s] (for [[w world] (:worlds s) [x v d] (:fdeps world) :when (= x :bundle)] [w v d]))
(defn end-exists? [s [kind w id]]
  (case kind :host true :run (boolean (m/run s w id)) :entity (boolean (m/ent s w id)) false))
(defn read-through-run? [s w r]
  (loop [w w]
    (when-let [p (and (= :following (get-in s [:worlds w :lineage :mode]))
                      (get-in s [:worlds w :lineage :parent]))]
      (or (boolean (m/run s p r)) (recur p)))))
(defn owned? [s w e] (seq (set/intersection #{:own :active :pin :settle} (m/reasons s w e))))
(defn dep-retained? [s w e] (= #{:dep} (m/reasons s w e)))
(defn bound? [s w e] (= #{:obl} (m/reasons s w e)))
(defn ev [id evidence] (when (seq evidence) {:id id :evidence (vec evidence)}))

(defn queued-events [s w]
  (concat (:queue (m/wr s w))
          (map :event (filter #(= w (:w %)) (get-in s [:env :outside])))))
(defn queued? [s w key value]
  (boolean (some #(= value (get % key)) (queued-events s w))))
(defn attached-cut-pending?
  "The sole event-free L20 case: an unpublished cut child with exact basis evidence."
  [s w o ob]
  (let [world (m/wr s w) [_ dw _] (:debtor ob)
        caps (m/caps-of s w)]
    (boolean
     (and (= :live (:status world)) (= :fenced (:admission world))
          (= 1 (count caps)) (every? #(false? (:published? (val %))) caps)
          (= :entity (first (:debtor ob))) (not= dw w)
          (= :run (first (:creditor ob)))
          (= :inherited (:origin ob))
          (= :inherited (:status (m/run s w (nth (:creditor ob) 2 nil))))
          (not-any? #(= :running (:status %)) (vals (:runs world)))
          (not-any? #(or (and (= w (:creditor-world %)) (= o (:o %)))
                         (and (= w (:join-bundle %)) (contains? (:members %) o)))
                    (queued-events s dw))
          (some (fn [[c cut]]
                  (let [source (:source-world ob) base (get-in cut [:basis source])
                        original (get-in base [:obligations o])]
                    (and (= :attached (:phase cut)) (= w (:child cut))
                         (= c (get-in world [:lineage :cut]))
                         (= (:basis cut) (get-in world [:lineage :basis]))
                         (contains? (get-in cut [:participants :worlds]) source)
                         (#{:admitted :pending-start} (get-in base [:copy-evidence o :phase]))
                         (= (:debtor original) (:debtor ob))
                         (= [:run source (nth (:creditor ob) 2)] (:creditor original))
                         (= :parked (get-in base [:runs (nth (:creditor ob) 2) :status])))))
                (:cuts s))))))

(defn pending-start? [s w o ob]
  (let [[kind dw e] (:debtor ob)]
    (boolean (and (= :entity kind) (not= dw w)
                  (or (attached-cut-pending? s w o ob)
                      (some #(or (and (= e (:start-for %)) (= w (:creditor-world %)) (= o (:o %)))
                                 (and (= w (:join-bundle %)) (= e (get-in % [:members o :debtor]))))
                            (queued-events s dw)))))))

(defn cancelled-in-flight? [s w o ob]
  (and (= :entity (first (:debtor ob))) (not= w (second (:debtor ob)))
       (queued? s w :cancelled o)))

(defn obligation-phases [s v o ob]
  (let [[_ w e] (:debtor ob) inherited? (= :inherited (:status (m/run s v (nth (:creditor ob) 2))))
        rows (:fdeps (m/wr s w))]
    (cond-> []
      (pending-start? s v o ob) (conj :pending-start)
      (cancelled-in-flight? s v o ob) (conj :cancelling)
      (and (m/ent s w e)
           (if inherited?
             (some (fn [[tag target d]] (and (= :bundle tag) (= v target) (contains? d e))) rows)
             (contains? rows [e v o]))) (conj :admitted))))

(defn l01
  "L1 one open, world-local owner; nil owner only idle/bound/dep-retained."
  [s]
  (vec (for [[w e er] (entities s)
             :when (if-let [owner (:owner er)] (not (m/open? s w owner))
                           (not (or (m/idle? s w e) (bound? s w e) (dep-retained? s w e) (contains? (:pins (m/wr s w)) e)
                                    (and (= :fork (:kind er)) (= #{:settle} (m/reasons s w e))))))]
         {:w w :e e :owner (:owner er) :reasons (m/reasons s w e)})))

(defn l02
  "L2 open run owners; at most one work/completed/stale; completed is newest completed, possibly below newer work."
  [s]
  (vec
   (concat
    (for [[w r rr] (runs s) :when (and (not= :unwinding (:status rr)) (not (m/open? s w (:owner rr))))]
      {:w w :r r :owner (:owner rr)})
    (for [[w world] (:worlds s) [e group] (group-by (comp :spin val) (:runs world))
          :let [work (filter #(m/work? (val %)) group)
                done (filter #(= :completed (:status (val %))) group)
                stale (filter #(= :stale (:status (val %))) group)
                newest (last (sort-by second (map key (remove #(= :stale (:status (val %))) group))))]
          :when (or (> (count work) 1) (> (count done) 1) (> (count stale) 1)

                    (some (fn [[old _]] (not-any? (fn [[r _]] (> (second r) (second old))) group)) stale))]
      {:w w :e e :runs (into {} group) :newest-nonstale newest}))))

(defn l03
  "L3 literal rule L after every committed transaction."
  [s]
  (vec (for [[w e er] (entities s)
             :when (not (or (seq (m/reasons s w e))
                            (and (m/idle? s w e) (seq (:tokens er)))))]
         {:w w :e e :row er})))

(defn l04
  "L4 closure of creations, spawned, pins, keyed instances, fdeps and fork ids."
  [s]
  (vec
   (concat
    (for [[w r rr] (runs s) e (:creations rr) :when (not (m/ent s w e))]
      {:index :creations :w w :r r :missing e})
    (for [[w r rr] (runs s) child (:spawned rr) :when (not (m/run s w child))]
      {:index :spawned :w w :r r :missing child})
    (for [[w r rr] (runs s) :when (and (not= :unwinding (:status rr)) (not (m/ent s w (:spin rr))))]
      {:index :run-spin :w w :r r :missing (:spin rr)})
    (for [[w world] (:worlds s) e (:pins world) :when (not (m/ent s w e))]
      {:index :pins :w w :missing e})
    (for [[w e er] (entities s) :when (#{:cache-row :keyed-entry} (:kind er))
          :when (not (m/ent s w (first e)))] {:index :instance :w w :e e})
    (for [[w e er] (entities s) :when (and (= :fork (:kind er)) (not (:reference? er)))
          :when (not (or ((:registry s) (second e))
                         (and (= :released (:status (m/wr s (second e))))
                              (queued? s w :fork-released (second e)))))] {:index :fork :w w :e e})
    (for [[w world] (:worlds s) ev (:queue world)
          :when (and (:custody-dispatch ev) (nil? (m/cap s (:cap ev))))]
      {:index :queue :w w :event ev})
    (for [[w v d] (bundles s) :when (not (and ((:registry s) v) (every? #(m/ent s w %) d)))]
      {:index :bundle :w w :v v :debtors d})
    (for [[w world] (:worlds s) [e v d :as fd] (:releasing world)
          :when (not (and (or (contains? (:registry s) v)
                              (and (= :released (:status (m/wr s v)))
                                   (queued? s w :fdep-ended fd)))
                          (if (= :bundle e) (every? #(m/ent s w %) d) (m/ent s w e))))]
      {:index :releasing :w w :row fd})
    (for [[w e v o] (fdeps s)
          :when (not (and ((:registry s) v) (get-in s [:worlds v :obligations o])
                          (m/ent s w e)))] {:index :fdeps :w w :e e :v v :o o}))))

(defn l05
  "L5 end existence, placement, standing flag and timer/external work creditor."
  [s]
  (vec (for [[w o ob] (obligations s)
             :let [[ck cw r] (:creditor ob) [dk dw _] (:debtor ob)]
             :when (or (not (end-exists? s (:creditor ob)))
                       (not (or (end-exists? s (:debtor ob))
                                (pending-start? s w o ob) (cancelled-in-flight? s w o ob)))
                       (not= (boolean (m/standing (:kind ob))) (:standing? ob))
                       (and (= :run ck) (not= w cw))
                       (and (= :host ck) (= :entity dk) (not= w dw))
                       (and (#{:timer :external} (:kind ob))
                            (not (and (= :run ck)
                                      (or (m/work? (m/run s w r))
                                          (and (= :inherited (:status (m/run s w r)))
                                               (:dormant? ob) (nil? (:token ob)))))))
                       (and (= :consumed (:slot ob)) (not (:standing? ob))))]
         {:w w :o o :row ob})))

(defn l06
  "L6 closed scopes have no owned rows, creditor ends or open children."
  [s]
  (vec (for [[w world] (:worlds s) [scope sr] (:scopes world)
             :when (= :closed (:status sr))
             :let [es (filter #(= scope (:owner (val %))) (:entities world))
                   rs (filter #(= scope (:owner (val %))) (:runs world))
                   os (filter #(= [:run w scope] (:creditor (val %))) (:obligations world))
                   children (filter #(and (= scope (:parent (val %)))
                                          (= :open (:status (val %)))) (:scopes world))]
             :when (some seq [es rs os children])]
         {:w w :scope scope :entities (vec es) :runs (vec rs)
          :obligations (vec os) :children (vec children)})))

(defn scope-errors
  "Open ownership is a rooted forest; acquisition balance charges scope storage."
  [s]
  (vec
   (mapcat
    (fn [[w world]]
      (when (not= :released (:status world))
        (let [root (:root world) scopes (:scopes world)
              explicit (dissoc scopes root)
              balance (:scope-balance world) high-water (:next-scope world)
              chain-error
              (fn [start]
                (loop [id start seen #{}]
                  (cond
                    (= id root) nil
                    (contains? seen id) {:start start :cycle id}
                    (not (m/open? s w id)) {:start start :missing-open-parent id}
                    :else (recur (if-let [rr (m/run s w id)] (:owner rr)
                                         (:parent (get scopes id))) (conj seen id)))))]
          (concat
           (when-not (and (= root [:root w]) (= :open (get-in scopes [root :status]))
                          (nil? (get-in scopes [root :parent])))
             [{:w w :invalid-root root}])
           (when-not (and (integer? balance) (not (neg? balance))
                          (= balance (count explicit)))
             [{:w w :scope-balance balance :scope-rows (count explicit)}])
           (when-not (and (integer? high-water) (not (neg? high-water)))
             [{:w w :invalid-scope-high-water high-water}])
           (for [[id row] explicit
                 :when (or (not (m/explicit-scope-id? id)) (m/run s w id)
                           (not= :open (:status row))
                           (and (m/explicit-scope-id? id) (number? high-water)
                                (>= (nth id 2) high-water)))]
             {:w w :invalid-scope id :row row :next-scope high-water})
           (for [id (concat (keys explicit)
                            (for [[id rr] (:runs world) :when (not= :unwinding (:status rr))] id))
                 :let [error (chain-error id)] :when error]
             (assoc error :w w)))))) (:worlds s))))

(defn l07
  "L7 idle caches own no run or owner, handle holds no result."
  [s]
  (vec (concat
        (for [[w e er] (entities s) :when (m/idle? s w e)
              :when (or (:owner er) (some #(and (= e (:spin %)) (not= :unwinding (:status %))) (vals (:runs (m/wr s w)))))]
          {:w w :e e :owner (:owner er) :runs (:runs (m/wr s w))})
        (for [[tok h] (get-in s [:env :handles]) :when (contains? h :result)]
          {:tok tok :handle h}))))

(defn l08
  "L8 every reachable touched incarnation covered; dropped incarnations excluded."
  [s]
  (vec (for [[tok h] (get-in s [:env :handles])
             w (set/union (:touched h) (:dropped h))
             :let [er (m/ent s w (:spin h)) present (contains? (:tokens er) tok)]
             :when (or (and (contains? (:dropped h) w) present)
                       (and (:reachable? h) (contains? (:touched h) w) (not (contains? (:dropped h) w)) er (not present)))]
         {:w w :tok tok :e (:spin h) :tokens (:tokens er) :handle h})))

(defn l09
  "L9 copy provenance is recorded on every copied row at the copy step."
  [s]
  (vec (for [[w world] (:worlds s) field [:entities :runs :obligations :scopes]
             [id row] (get world field) :let [og (:origin row) mode (get-in world [:lineage :mode])]
             :when (or (and og (not (#{:created :copied :inherited} og)))
                       (and (= :copied og) (not= :following mode))
                       (and (= :inherited og) (= :root mode))
                       (and (#{:copied :inherited} og)
                            (or (nil? (:source-world row)) (= w (:source-world row))
                                (not (contains? (:known-worlds s) (:source-world row)))))
                       (and (= field :entities) (= :fork (:kind row)) (#{:copied :inherited} og) (not (:reference? row))))]
         {:w w :field field :id id :row row})))

(defn expected-fdeps [s include-inherited?]
  (set (for [[v o ob] (obligations s)
             :let [[dk w e] (:debtor ob) [_ _ r] (:creditor ob)]
             :when (and (= dk :entity) (not= w v) (= :run (first (:creditor ob)))
                        (not (pending-start? s v o ob)) (not (cancelled-in-flight? s v o ob))
                        (or include-inherited? (not= :inherited (:status (m/run s v r)))))]
         [w e v o])))

(defn l10
  "L10 exact ordinary and aggregate dependencies, plus one event per releasing row."
  [s]
  (let [actual (fdeps s) expected (expected-fdeps s false)
        inherited (set/difference (expected-fdeps s true) expected)
        expected-bundles (set (for [[[w v] rows] (group-by (fn [[w _ v _]] [w v]) inherited)]
                                [w v (set (map second rows))]))
        actual-bundles (set (bundles s))]
    (vec (concat
          (for [[v o ob] (obligations s)
                :let [[dk w _] (:debtor ob)]
                :when (and (= :entity dk) (not= w v) (= :run (first (:creditor ob)))
                           (not= 1 (count (obligation-phases s v o ob))))]
            {:v v :o o :phases (obligation-phases s v o ob)})
          (for [x (set/difference expected actual)] {:missing x})
          (for [x (set/difference actual expected)] {:extra x})
          (for [x (set/difference expected-bundles actual-bundles)] {:missing-bundle x})
          (for [x (set/difference actual-bundles expected-bundles)] {:extra-bundle x})
          (for [[w world] (:worlds s) fd (:releasing world)
                :let [events (concat (:queue world)
                                     (map :event (filter #(= w (:w %)) (get-in s [:env :outside]))))
                      matches (filter #(= fd (:fdep-ended %)) events)]
                :when (not= 1 (count matches))]
            {:w w :releasing fd :events (vec matches)})
          (for [[w world] (:worlds s) [e v o :as fd] (:releasing world)
                :when (if (= :bundle e)
                        (some (fn [[cv _ ob]]
                                (and (= cv v) (= :entity (first (:debtor ob)))
                                     (= w (second (:debtor ob)))
                                     (contains? o (nth (:debtor ob) 2))
                                     (= :inherited (:status (m/run s v (nth (:creditor ob) 2))))))
                              (obligations s))
                        (= [:entity w e] (get-in s [:worlds v :obligations o :debtor])))]
            {:w w :releasing-open-dependency fd})))))

(defn l11
  "L11 ordinary and aggregate dependencies always name existing storage."
  [s]
  (vec (concat (for [[w e v o] (fdeps s) :when (not (m/ent s w e))]
                 {:w w :e e :creditor-world v :o o})
               (for [[w v d] (bundles s) e d :when (not (m/ent s w e))]
                 {:w w :e e :creditor-world v :bundle d}))))

(defn plain-value? [x]
  (cond (or (nil? x) (boolean? x) (number? x) (string? x) (keyword? x)
            (symbol? x) (char? x)) true
        (map? x) (and (not (record? x)) (every? plain-value? (keys x))
                      (every? plain-value? (vals x)))
        (coll? x) (every? plain-value? x)
        :else false))
(defn l12
  "L12 no host objects, except an obligation's cont slot."
  [s]
  (let [state (update s :worlds
                      #(into {} (for [[w world] %]
                                  [w (update world :obligations
                                             (fn [obs] (into {} (for [[o ob] obs] [o (dissoc ob :cont)]))))])))]
    (if (plain-value? state) [] [{:non-data-state true}])))

(def census-constant 8)
(defn census [world]
  {:pins (count (:pins world)) :fdeps (count (:fdeps world)) :releasing (count (:releasing world))
   :creations (reduce + 0 (map #(count (:creations %)) (vals (:runs world))))
   :spawned (reduce + 0 (map #(count (:spawned %)) (vals (:runs world))))
   :queue (count (:queue world))
   :scopes (count (:scopes world))
   :scope-parents (count (filter :parent (vals (:scopes world))))})
(defn l13
  "L13 extended denominator, fixed c=8, logical dependency members; no waiver for releasing."
  [s]
  (vec (mapcat
        (fn [[w world]]
          (let [n (+ (count (:entities world)) (count (:runs world)) (count (:obligations world))
                     (count (filter #(not (m/terminal (:disposition (val %)))) (m/caps-of s w)))
                     (count (filter #(and (m/active-cuts (:phase %))
                                          (contains? (get-in % [:participants :worlds]) w)) (vals (:cuts s)))))
                deps (count (filter #(dep-retained? s w %) (keys (:entities world))))
                members (fn [rows] (reduce + 0 (map (fn [[e _ d]] (if (= :bundle e) (count d) 1)) rows)))
                fd (members (set/union (:fdeps world) (:releasing world)))
                in-flight (members (filter #(queued? s w :fdep-ended %) (:releasing world)))
                control (count (set (keep m/control-key (:queue world))))
                obs (count (filter #(let [[k dw _] (:debtor (nth % 2))]
                                      (and (= :entity k) (= dw w) (not= w (first %))))
                                   (obligations s)))]
            (concat (let [unwinding (count (filter #(= :unwinding (:status %)) (vals (:runs world))))
                          threads (count (filter #(and (= w (:world %)) (:run %))
                                                 (vals (get-in s [:env :threads]))))
                          native (count (filter #(and (= w (first (:owner %))) (not= :joined (:state %)))
                                                (vals (get-in s [:env :native]))))]
                      (when (> unwinding (+ threads native))
                        [{:w w :unwinding unwinding :threads threads :unjoined native}]))
                    (for [[index size] (census world)
                          :let [scope-index? (#{:scopes :scope-parents} index)
                                limit (if scope-index?
                                        (+ (if (= :scopes index) 1 0) (get world :scope-balance 0))
                                        (+ (* census-constant n) (* census-constant control)))]
                          :when (> size limit)]
                      {:w w :index index :size size :rows n :control control :c census-constant :limit limit})
                    (when (not (<= deps fd (+ obs in-flight))) [{:w w :dep-retained deps :fdeps fd :obligations obs :in-flight in-flight}])
                    (for [[key events] (group-by m/control-key
                                                 (concat (:queue world)
                                                         (map :event (filter #(= w (:w %)) (get-in s [:env :outside])))))
                          :when (and key (> (count events) 1))]
                      {:w w :duplicate-control key :count (count events)}))))
        (:worlds s))))

(defn l14
  "L14 inherited runs belong to fork scopes and are neither work nor quiescence blockers."
  [s]
  (vec (concat
        (for [[w world] (:worlds s)
              :when (and (not-any? m/busy? (vals (:runs world)))
                         (some #(and (#{:timer :external} (:kind %))
                                     (= :inherited (:status (m/run s w (nth (:creditor %) 2 nil)))))
                               (vals (:obligations world)))
                         (not (m/quiescent? s w)))]
          {:w w :inherited-blocks-quiescence true})
        (for [[w r rr] (runs s) :when (= :inherited (:status rr))
              :when (or (= :root (get-in s [:worlds w :lineage :mode]))
                        (not (m/open? s w (:owner rr))) (m/work? rr)
                        (and (= :following (get-in s [:worlds w :lineage :mode]))
                             (not= (:owner rr) (:root (m/wr s w)))))] {:w w :r r :row rr})
        (for [[w o ob] (obligations s) :when (and (= :run (first (:creditor ob)))
                                                  (not= w (second (:creditor ob))))]
          {:w w :o o :creditor (:creditor ob)}))))

(defn l15
  "L15 selected world of every executing slice. Historical slices checked in TL15."
  [s]
  (vec (for [[th thread] (get-in s [:env :threads]) :when (:executing? thread)
             :when (or (nil? (:world thread))
                       (not= (:world thread) (:obligation-world thread))
                       (and (not= :released (:status (m/wr s (:world thread))))
                            (not (m/run s (:world thread) (:run thread))))
                       (not (:run thread)))]
         {:thread th :slice thread})))

(defn l16
  "L16 sealed seq fence and quiescent/joined prepared capability."
  [s]
  (vec (concat
        (for [[w world] (:worlds s) :when (= :sealed (:status world))
              :when (or (not= :fenced (:admission world))
                        (some #(> (:seq %) (:seal-seq world)) (vals (:runs world))))]
          {:w w :admission (:admission world) :seal-seq (:seal-seq world) :runs (:runs world)})
        (for [[k cap] (m/all-caps s)
              :when (or (#{:settling :incomplete} (:disposition cap))
                        (and (m/terminal (:disposition cap))
                             (#{:merge :discard} (:kind (m/record s (:op cap))))))
              :let [w (:world cap) world (m/wr s w)
                    ;; Observe the tables independently of the transition's
                    ;; quiescent?/joined? predicates, including ordinary tails.
                    work (for [[r rr] (:runs world)
                               :when (#{:running :parked :unwinding} (:status rr))] r)
                    waits (for [[o ob] (:obligations world)
                                :when (and (#{:timer :external} (:kind ob))
                                           (not= :inherited (:status (get (:runs world) (nth (:creditor ob) 2 nil)))))] o)
                    threads (for [[th row] (get-in s [:env :threads])
                                  :when (and (= w (:world row)) (:run row))] th)
                    native (for [[n row] (get-in s [:env :native])
                                 :when (and (= w (first (:owner row))) (not= :joined (:state row)))] n)]
              :when (some seq [work waits threads native])]
          {:k k :world w :disposition (:disposition cap)
           :work (vec work) :waits (vec waits) :threads (vec threads) :native (vec native)}))))

(defn l17
  "L17 disjoint live authority, total scope cover and one terminal consuming op."
  [s]
  (vec (mapcat
        (fn [[w caps]]
          (let [root-scopes (map (comp :scope val) (filter #(nil? (:pred (val %))) caps))
                original (apply set/union #{} root-scopes)
                leaves (filter #(or (not (m/terminal (:disposition (val %))))
                                    (#{:merged :discarded} (:disposition (val %)))) caps)
                live (filter #(not (m/terminal (:disposition (val %)))) caps)]
            (concat
             (when (not= original (apply set/union #{} (map (comp :scope val) leaves)))
               [{:w w :expected original :leaves (into {} leaves)}])
             (for [[k cap] live [j other] live :when (neg? (compare (pr-str k) (pr-str j)))
                   :when (seq (set/intersection (:scope cap) (:scope other)))]
               {:w w :overlap [k j]})
             (for [[k cap] caps :when (and (m/terminal (:disposition cap)) (nil? (:op cap)))]
               {:w w :k k :missing-op true})
             (for [[k cap] caps :when (#{:transferred :partitioned} (:disposition cap))
                   :let [scopes (map #(:scope (or (m/cap s %) (get (m/vanished-caps s) %))) (:successors cap))]
                   :when (or (not= (:scope cap) (apply set/union #{} scopes))
                             (not= (count (:scope cap)) (reduce + 0 (map count scopes))))]
               {:w w :k k :successor-scopes (vec scopes)}))))
        (group-by (comp :world val) (merge (m/all-caps s) (m/vanished-caps s))))))

(defn l18
  "L18 durable evidence, witnessed terminal, effect/base release ordering."
  [s]
  (vec (concat
        (for [[k cap] (m/all-caps s)
              :when (or (not= (:durable? cap) (m/durable-scope? s (:scope cap)))
                        (not= (:durable? cap) (contains? (get-in s [:durable :caps]) k))
                        (and (:restarted? s) (:durable? cap) (= :open (:disposition cap))))]
          {:k k :durability cap})
        (for [[op rec] (m/all-records s)
              :when (not= (:durable? (m/cap s (:cap rec))) (contains? (get-in s [:durable :records]) op))]
          {:op op :record-location rec})
        (for [[k cap] (m/all-caps s)
              :let [rec (m/record s (:op cap))]
              :when (or (and (#{:settling :incomplete :merged :discarded} (:disposition cap))
                             (nil? rec))
                        (and (#{:merged :discarded} (:disposition cap))
                             (not-every? #(and (= :done (:status %)) (:witness %)) (:steps rec))))]
          {:k k :cap cap :record rec})
        (for [[op rec] (m/all-records s)
              :let [cap (m/cap s (:cap rec))]
              :when (or (and (:effects-released? rec) (not (m/terminal (:disposition cap))))
                        (and (not (:effects-released? rec))
                             (seq (set/intersection (:freed-bases s) (set (vals (:bases rec)))))))]
          {:op op :record rec :cap cap :freed (:freed-bases s)})
        (for [[k cap] (m/all-caps s)
              :when (and (not (m/terminal (:disposition cap)))
                         (seq (set/intersection (:freed-bases s) (set (vals (:bases cap))))))]
          {:k k :needed-bases (:bases cap) :freed (:freed-bases s)}))))

(defn l19
  "L19 incomplete operations retain a sealed runtime and unreleased effects."
  [s]
  (vec (for [[k cap] (m/all-caps s) :when (= :incomplete (:disposition cap))
             :let [w (:world cap) rec (m/record s (:op cap))]
             :when (or (and (m/wr s w) (not= :sealed (:status (m/wr s w)))) (:effects-released? rec)
                       (and (m/wr s w) (not= :fenced (:admission (m/wr s w)))))]
         {:k k :w w :world (m/wr s w) :record rec})))

(defn l20
  "L20 exact tombstones; local cleanup events or the attached-cut basis case."
  [s]
  (vec (mapcat
        (fn [[v world]]
          (when (= :released (:status world))
            (concat
             (when (or (contains? (:registry s) v)
                       (not= #{:id :lineage :status} (set (keys world))))
               [{:w v :tombstone world :registered? (contains? (:registry s) v)}])
             (for [[k cap] (m/caps-of s v) :when (not (m/terminal (:disposition cap)))]
               {:w v :open-cap k})
             (for [[w other] (:worlds s) fd (:fdeps other) :when (= v (second fd))]
               {:w w :released v :live-fdep fd})
             (for [[w o ob] (obligations s)
                   :when (and (= :entity (first (:debtor ob))) (= v (second (:debtor ob)))
                              (not (queued? s w :cancelled o))
                              (not (attached-cut-pending? s w o ob)))]
               {:w w :released v :obligation o :missing :cancelled})
             (for [[w other] (:worlds s) fd (:releasing other)
                   :when (and (= v (second fd)) (not (queued? s w :fdep-ended fd)))]
               {:w w :released v :releasing fd :missing :fdep-ended})
             (for [[w e er] (entities s)
                   :when (and (= [:fork v] e) (not (:reference? er))
                              (not (queued? s w :fork-released v)))]
               {:w w :released v :fork e :missing :fork-released}))))
        (:worlds s))))

(defn l21
  "L21 immutable known lineage; registry literally contains only :live worlds."
  [s]
  (vec (concat
        (for [[w world] (:worlds s) :let [lin (:lineage world) parent (:parent lin)]
              :when (or (nil? lin) (not= lin (get-in s [:lineages w]))
                        (not= (= :root (:mode lin)) (nil? parent))
                        (and parent (not ((:known-worlds s) parent)))
                        (contains? world :parent-ctx))]
          {:w w :lineage lin :original (get-in s [:lineages w])})
        (for [w (set/union (:registry s) (set (keys (:worlds s))))
              :when (not= (contains? (:registry s) w)
                          (and (boolean (m/wr s w)) (not= :released (:status (m/wr s w)))))]
          {:registry-world w :status (:status (m/wr s w))}))))

(defn basis-queue
  "Independent copy-envelope scan over the captured admitted and held queues."
  [base child]
  (let [source (:id base)
        events (concat (:queue base) (map :event (:held base)))
        copies (:obligations child)
        reissued (for [event events [o original] (:obligations base)
                       :let [copy (get copies o)] :when copy
                       :when (or (= o (:cancelled event))
                                 (and (= (nth (:debtor original) 2 nil) (:completion event))
                                      (= (second (:debtor original)) (get event :debtor-world source))))]
                   (cond-> event (:completion event) (assoc :debtor-world (second (:debtor copy)))))]
    (mapv #(assoc %1 :seq %2) (distinct (sort-by :seq reissued)) (range 1 (inc (count reissued))))))

(defn captured-evidence [s w]
  (into {} (for [[o ob] (:obligations (m/wr s w))]
             [o {:phase (if (and (= :entity (first (:debtor ob))) (not= w (second (:debtor ob))))
                          (first (obligation-phases s w o ob)) :admitted)
                 :cancelled (first (filter #(= o (:cancelled %)) (queued-events s w)))
                 :completions (vec (filter #(and (= (nth (:debtor ob) 2 nil) (:completion %))
                                                 (= (second (:debtor ob)) (get % :debtor-world w)))
                                           (queued-events s w)))}])))

(defn l22
  "L22 cut fences, exclusion, exclusive permits and exact attached basis."
  [s]
  (vec (mapcat
        (fn [[c cut]]
          (let [worlds (get-in cut [:participants :worlds])
                components (get-in cut [:participants :components])
                perms (get-in s [:env :threads (:coordinator cut) :excl-permits])]
            (concat
             (for [w worlds :when (and (m/active-cuts (:phase cut))
                                       (not= :fenced (:admission (m/wr s w))))]
               {:c c :w w :missing-fence true})
             (when (and (= :p1q (:protocol cut)) (m/active-cuts (:phase cut)))
               (concat
                (when-not (#{:ready :captured :attached} (:phase cut))
                  [{:c c :quiescent-cut-phase (:phase cut)}])
                (for [w worlds [r rr] (:runs (m/wr s w)) :when (#{:running :unwinding} (:status rr))]
                  {:c c :w w :running r})
                (for [w worlds event (:queue (m/wr s w))]
                  {:c c :w w :admitted-after-readiness event})
                (for [[n nr] (get-in s [:env :native])
                      :when (and (worlds (first (:owner nr))) (not= :joined (:state nr))
                                 (not (:boundary? nr)))]
                  {:c c :native-not-at-boundary n})))
             (for [[d other] (:cuts s) :when (and (not= c d) (m/active-cuts (:phase cut))
                                                  (m/active-cuts (:phase other))
                                                  (or (seq (set/intersection worlds (get-in other [:participants :worlds])))
                                                      (seq (set/intersection (get-in cut [:participants :systems]) (get-in other [:participants :systems])))))]
               {:overlapping-cuts [c d]})
             (when (and (#{:captured :attached} (:phase cut))
                        (or (not= (set perms) components)
                            (not= perms (vec (sort components)))
                            (some #(seq (set/intersection components (:read-permits %)))
                                  (vals (get-in s [:env :threads])))))
               [{:c c :permits perms :expected components}])
             (when (and (= :attached (:phase cut)) (not= :fenced (:admission (m/wr s (:child cut)))))
               [{:c c :child (:child cut) :not-fenced true}])
             (when (and (= :attached (:phase cut))
                        (not (and (= 1 (count (m/caps-of s (:child cut))))
                                  (every? #(false? (:published? (val %))) (m/caps-of s (:child cut))))))
               [{:c c :child (:child cut) :capability-not-unpublished true}])
             (when (= :attached (:phase cut))
               (let [w (first (keys (:basis cut))) v (:child cut)
                     transformed (m/copy-basis s (:basis cut) w v (:mode cut))
                     expected (assoc transformed :queue (basis-queue (get-in cut [:basis w]) transformed))
                     actual (m/wr s v)]
                 (for [field [:entities :runs :obligations :pins :queue :fdeps :releasing]
                       :when (not= (get expected field) (get actual field))]
                   {:c c :child v :field field :expected (get expected field) :actual (get actual field)}))))))
        (:cuts s))))

(defn l23
  "L23 keyed signals use lineage keyid; cache keys carry a spin instance owner."
  [s]
  (vec (for [[w e er] (entities s)
             :when (or (and (:key er) (not= e (m/keyid s w (:key er))))
                       (and (#{:cache-row :keyed-entry} (:kind er))
                            (not (and (vector? e) (= 2 (count e))
                                      (m/ent s w (first e)) (:owner er)))))]
         {:w w :e e :row er})))

(defn l24
  "L24 registered waiters require an open external obligation or armed token."
  [s]
  (vec (for [[token waiter] (get-in s [:env :waiters])
             :let [ob (get-in s [:worlds (:world waiter) :obligations (:o waiter)])]
             :when (or (and (:registered? waiter)
                            (not (or (:armed? waiter) (= :external (:kind ob)))))
                       (and (:armed? waiter) (not (:registered? waiter))))]
         {:token token :waiter waiter :obligation ob})))

(defn l25
  "L25 exact retired (cancelled, superseded or normalised)/physical equivalence, no ownership, obligations or indexes.
  Retirement provenance on thread/native links survives removal of the run."
  [s]
  (vec
   (concat
    (for [[w r rr] (runs s)
          :let [world (m/wr s w)
                threads (filter #(and (= w (:world %)) (= r (:run %)))
                                (vals (get-in s [:env :threads])))
                native (filter #(and (= [w r] (:owner %)) (not (cleanup/mailbox-callback? %)) (not= :joined (:state %)))
                               (vals (get-in s [:env :native])))
                retired? (or (:retired? rr) (some :retired? threads) (some #(and (not (cleanup/mailbox-callback? %)) (:retired? %)) native))
                expected? (and retired? (or (seq threads) (seq native)))
                unwinding? (= :unwinding (:status rr))
                indexed? (or (:owner rr) (seq (:creations rr)) (seq (:spawned rr)) (:pred rr)
                             (some #(or (= r (:owner %)) (= r (:creator %))) (vals (:entities world)))
                             (some #(or (= r (:owner %)) (= r (:pred %)) (contains? (:spawned %) r))
                                   (vals (:runs world)))
                             (some #(= r (:parent %)) (vals (:scopes world)))
                             (some #(= [:run w r] (:creditor %)) (vals (:obligations world))))
                malformed? (or (not (:retired? rr)) indexed?
                               (not (and (vector? (:anchor rr)) (= r (first (:anchor rr)))
                                         (= w (last (:anchor rr))))))]
          :when (or (not= (boolean expected?) unwinding?) (and unwinding? malformed?))]
      {:w w :r r :unwinding? unwinding? :retired? (boolean retired?)
       :threads (vec threads) :unjoined (vec native) :indexed? (boolean indexed?) :row rr})
    (for [[th tr] (get-in s [:env :threads])
          :when (and (:retired? tr) (:run tr)
                     (not= :released (:status (m/wr s (:world tr))))
                     (not= :unwinding (:status (m/run s (:world tr) (:run tr)))))]
      {:thread th :retired-slice-without-unwinding tr})
    (for [[n nr] (get-in s [:env :native]) :let [[w r] (:owner nr)]
          :when (and (not (cleanup/mailbox-callback? nr)) (:retired? nr) (not= :joined (:state nr))
                     (not= :released (:status (m/wr s w)))
                     (not= :unwinding (:status (m/run s w r))))]
      {:native n :retired-op-without-unwinding nr}))))

(defn l26
  "L26 adoption ancestry contains only older same-spin generations with semantic references."
  [s]
  (vec (for [[w r rr] (runs s)
             :let [world (m/wr s w)
                   relevant (into (set (for [[id row] (:runs world)
                                             :when (not= :unwinding (:status row))] id))
                                  (keep :creator (vals (:entities world))))]
             :when (or (not (set? (:ancestors rr)))
                       (and (= :unwinding (:status rr)) (seq (:ancestors rr)))
                       (some #(or (not (contains? relevant %))
                                  (not= (first r) (first %))
                                  (not (< (second %) (second r)))) (:ancestors rr)))]
         {:w w :r r :ancestors (:ancestors rr)})))

(defn mailbox-stores [s]
  (let [ids (set (concat
                  (for [[w world] (:worlds s) [e row] (:entities world) :when (= :mailbox (:kind row))]
                    [w e (:allocation row)])
                  (for [[key row] (get-in s [:env :cleanup-cells]) :when (= :mailbox (:kind row))]
                    [(first key) (nth key 2) (:allocation row)])))]
    (into {} (for [[w e allocation :as id] ids]
               [id (cleanup/mailbox-control s w e allocation)]))))

(defn mailbox-message-locations [s]
  (concat
   (for [[[w e _] control] (mailbox-stores s)
         message (concat (:messages control) (map (fn [[_ row]] {:id (:message-id row)}) (:reservations control)))]
     [w e (:id message)])
   (for [[w event] (concat (for [[w world] (:worlds s) event (:queue world)] [w event])
                           (map (juxt :w :event) (get-in s [:env :outside])))
         :when (:mailbox-post event)] [w (:mailbox-post event) (:message-id event)])))

(defn mailbox-errors [s]
  (vec
   (concat
    (for [[message count] (frequencies (mailbox-message-locations s)) :when (> count 1)]
      {:message message :duplicate-mailbox-message count})
    (for [[w world] (:worlds s) [e row] (:entities world) :when (= :mailbox (:kind row))
          :when (or (not= e (:allocation row)) (:completed? row) (some? (:result row)))]
      {:w w :e e :invalid-mailbox-source row})
    (for [[[w e allocation] control] (mailbox-stores s)
          :let [pending (:pending control) consumers (:consumers control)
                messages (concat (:messages control) (map (fn [[_ r]] {:id (:message-id r) :value (:value r)})
                                                          (:reservations control)))]
          :when (or (not= #{:messages :consumers :pending :reservations :protected :physical} (set (keys control)))
                    (not (vector? (:messages control))) (not (vector? consumers))
                    (not= (count consumers) (count (set consumers)))
                    (not= (set consumers) (set (keys pending)))
                    (not= (:protected control)
                          (into {} (for [[_ row] pending :when (= :operation (:kind row))]
                                     [(:reg row) {:operation (:op row) :sequence (second (:op row))}])))
                    (and (seq (:messages control)) (seq consumers))
                    (not= (count messages) (count (set (map :id messages))))
                    (some #(not= allocation (first (:id %))) messages))]
      {:w w :e e :invalid-mailbox-control control})
    (for [[[w e allocation] control] (mailbox-stores s)
          [consumer row] (concat (:pending control) (:reservations control))
          :let [pending? (contains? (:pending control) consumer)
                ob (get-in s [:worlds w :obligations (:o row)])
                operation (cleanup/operation s (:op row))
                reg (get-in operation [:registrations (:reg row)])]
          :when (or (not (#{:ordinary :host :operation} (:kind row)))
                    (not= consumer (case (:kind row) :ordinary [:obligation (:o row)] :host [:host (:o row)]
                                         :operation [:operation (:reg row)] nil))
                    (if pending?
                      (or (contains? row :message-id) (contains? row :state))
                      (or (not (contains? row :value)) (not (#{:reserved :claimed :entered} (:state row)))))
                    (case (:kind row)
                      :operation (or (nil? reg)
                                     (not= (if pending? :pending (case (:state row) :reserved :ready :claimed :claimed :entered :claimed))
                                           (:state reg))
                                     (not= (when-not pending? (:message-id row)) (:message-id reg))
                                     (and (not pending?) (not= (:value row) (:delivery reg)))
                                     (not= pending? (contains? (:protected control) (:reg row))))
                      (:ordinary :host) (and (or pending? (= :reserved (:state row)))
                                             (or (nil? ob) (not= :armed (:slot ob))
                                                 (not= [:entity w e] (:debtor ob))))
                      true))]
      {:w w :e e :consumer consumer :invalid-mailbox-consumer row})
    (for [[[w e allocation] control] (mailbox-stores s) [frame physical] (:physical control)
          :let [consumer (:consumer physical) owner (second (:owner physical))
                receipt [:mailbox-callback w owner consumer] row (get-in s [:env :native receipt])
                reservation (get-in control [:reservations consumer])]
          :when (or (not (cleanup/mailbox-callback? row))
                    (not= [w owner] (:owner row)) (not= frame (:frame row))
                    (not= allocation (:allocation row)) (not= (:kind physical) (:consumer-kind row))
                    (not= (:anchor physical) (:anchor row))
                    (and (not= :error (:variant row))
                         (or (not (#{:claimed :entered} (:state reservation))) (not= frame (:frame reservation)))))]
      {:w w :e e :frame frame :orphan-mailbox-physical physical})
    (for [[receipt row] (get-in s [:env :native]) :when (cleanup/mailbox-callback? row)
          :let [[w owner] (:owner row) e (:allocation row) control (cleanup/mailbox-control s w e e)
                physical (get-in control [:physical (:frame row)])]
          :when (or (not= receipt [:mailbox-callback w owner (:consumer row)])
                    (not= :running (:state row))
                    (if (= :queued (:phase row))
                      (or (:physical? row) physical (not= :error (:variant row)))
                      (or (not= :executing (:phase row)) (not (:physical? row))
                          (not= (:consumer row) (:consumer physical))))
                    (and (not (get-in s [:worlds w :entities e :owner])) (not (:retired? row)))
                    (not= owner (first (:anchor row))) (not= w (last (:anchor row))))]
      {:receipt receipt :orphan-mailbox-receipt row})
    (for [[key cell] (get-in s [:env :cleanup-cells]) :when (= :mailbox (:kind cell))
          :let [[w _ e] key canonical (cleanup/mailbox-control s w e (:allocation cell))]
          :when (not= canonical (:mailbox cell))]
      {:cell key :inconsistent-mailbox-resource {:expected canonical :actual (:mailbox cell)}}))))

(defn- mailbox-unentered [s]
  (reduce
   (fn [all [[w e allocation] control]]
     (reduce (fn [all message] (assoc all [w e (:id message)] (:value message))) all
             (concat (:messages control)
                     (for [[_ row] (:reservations control) :when (not= :entered (:state row))]
                       {:id (:message-id row) :value (:value row)}))))
   (into {} (for [[w event] (concat (for [[w world] (:worlds s) event (:queue world)] [w event])
                                    (map (juxt :w :event) (get-in s [:env :outside])))
                  :when (:mailbox-post event)]
              [[w (:mailbox-post event) (:message-id event)] (:value event)]))
   (mailbox-stores s)))

(defn process-loss? [action]
  (and (= :t31 (:t action)) (not= :restart (:phase action))))

(defn mailbox-edge-errors [{:keys [before action after refusal observation]}]
  (when (and (not refusal) (not observation) (not (process-loss? action)))
    (let [old (mailbox-unentered before) current (mailbox-unentered after)
          stores-before (mailbox-stores before) stores-after (mailbox-stores after)
          entered (for [ev (:events after)
                        :when (or (#{:mailbox-entry :mailbox-immediate} (:event ev))
                                  (and (= :continuation-entry (:event ev)) (:message-id ev)))] ev)
          entered-keys (set (for [ev entered]
                              [(or (:world ev) (first (get-in before [:env :native (first (:op ev)) :owner])))
                               (or (:e ev) (get-in before [:env :native (first (:op ev)) :operation :registrations (:reg ev) :e]))
                               (:message-id ev)]))
          new-posts (when (= :mailbox-post-request (:t action))
                      {[(:w action) (:e action)
                        [(:allocation action) (inc (max (get-in before [:worlds (:w action) :seq] 0)
                                                        (get-in before [:clocks (:w action)] 0)))]] (:value action)})]
      (vec
       (concat
        (for [[receipt row] (get-in before [:env :native]) :when (cleanup/mailbox-callback? row)
              :let [actual (get-in after [:env :native receipt])
                    [w _] (:owner row) e (:allocation row)
                    reservation (get-in stores-before [[w e e] :reservations (:consumer row)])
                    valid-return? (and (= :mailbox-return (:t action)) (= (:consumer row) (:consumer action))
                                       (= (:frame row) (:frame action)) (= :executing (:phase row)) (:physical? row)
                                       (or (= :error (:variant row)) (= :entered (:state reservation))))]
              :when (if actual (not= (:cells row) (:cells actual)) (not valid-return?))]
          {:receipt receipt :mailbox-physical-conservation {:before row :after actual :action action}})
        (for [[key value] old :let [[w e mid] key]
              :when (and (get stores-after [w e e])
                         (not (contains? entered-keys key))
                         (or (not (contains? current key)) (not= value (get current key))))]
          {:message key :lost-mailbox-input {:before value :after (get current key)}})
        (for [[key value] current
              :when (and (not (contains? old key))
                         (not (some #(= key (first %)) new-posts)))]
          {:message key :invented-mailbox-input value})
        (for [key entered-keys :when (or (not (contains? old key)) (contains? current key))]
          {:message key :invalid-mailbox-entry-conservation true})
        (when (= :mailbox-post (:t action))
          (let [w (:w action) e (:e action)
                control (get stores-before [w e (:allocation action)])
                front (or (first (:queue (m/wr before w)))
                          (:event (first (filter #(= w (:w %)) (get-in before [:env :outside])))))
                expected {:event :mailbox-post :world w :e e :message-id (:message-id front)
                          :consumer (first (:consumers control)) :value (:value front)}]
            (when (and control (not (some #{expected} (:events after))))
              [{:e e :mailbox-fifo-selection {:expected expected :events (:events after)}}])))
        (for [ev entered
              :let [key [(or (:world ev) (first (get-in before [:env :native (first (:op ev)) :owner])))
                         (or (:e ev) (get-in before [:env :native (first (:op ev)) :operation :registrations (:reg ev) :e]))
                         (:message-id ev)]]
              :when (not= (get old key) (:value ev))]
          {:message key :counterfeit-mailbox-entry {:expected (get old key) :actual (:value ev)}}))))))

(defn timer-errors
  "Typed timer identity, logical wait and independent physical/disposal barriers."
  [s]
  (vec
   (concat
    (for [[n row] (get-in s [:env :native]) :when (cleanup/timer-resource? row)
          :let [[w r] (:owner row) o (:o row) ob (get-in s [:worlds w :obligations o])
                armed? (= :armed (:phase row)) installer (get-in s [:env :threads (:installer row)])]
          :when (or (not= n [:timer w o]) (not= :running (:state row))
                    (not (#{:armed :fired :failed :revoked} (:phase row)))
                    (not (#{:pending :seated :none :failed} (:install row)))
                    (not (#{:none :present :release-pending :release-claimed :released :failed} (:handle row)))
                    (not (set? (:frames row)))
                    (not (set/subset? (:frames row) #{[:timer-frame n 0]}))
                    (and (seq (:frames row)) (not (#{:fired :failed} (:phase row))))
                    (not= armed? (contains? row :value))
                    (and armed? (not (and (= :timer (:kind ob)) (= n (:timer ob))
                                          (= [:run w r] (:creditor ob)) (= :armed (:slot ob))
                                          (= :parked (:status (m/run s w r))))))
                    (and (not armed?) (= n (:timer ob)))
                    (and (= :pending (:install row))
                         (not (and (= [w r] [(:world installer) (:run installer)]) (:executing? installer))))
                    (and (#{:pending :none :failed} (:install row)) (not= :none (:handle row)))
                    (and armed? (not (#{:none :present} (:handle row))))
                    (and (not armed?) (= :present (:handle row)))
                    (not= (:anchor row) (if (:retired? row) (:anchor row) (m/owner-chain s w r)))
                    (not (and (vector? (:anchor row)) (= r (first (:anchor row))) (= w (last (:anchor row)))))
                    (and (not armed?) (not= :pending (:install row)) (empty? (:frames row))
                         (#{:none :released :failed} (:handle row))))]
      {:timer n :row row :obligation ob})
    (for [[w world] (:worlds s) [o ob] (:obligations world) :when (:timer ob)
          :let [row (get-in s [:env :native (:timer ob)])]
          :when (not (and (cleanup/timer-resource? row) (= :armed (:phase row))
                          (= o (:o row)) (= (:creditor ob) (into [:run] (:owner row)))))]
      {:w w :o o :unbacked-timer ob}))))

(defn timer-edge-errors
  "Conserve admitted callback frames and registered data independently of indices."
  [{:keys [before action after refusal]}]
  (when (and (not refusal) (not= :join (:t action)) (not (process-loss? action)))
    (let [t (:t action) n (:n action) old (get-in before [:env :native n])
          [w r] (:owner old) o (:o old) ob (get-in before [:worlds w :obligations o])
          fires? (and (= :timer-fire t) (cleanup/timer-resource? old) (= :armed (:phase old))
                      (= w (:w action)) (= :live (:status (m/wr before w)))
                      (= :open (:admission (m/wr before w))) (= :parked (:status (m/run before w r)))
                      (= r (m/current before w (first r))) (= n (:timer ob)) (= :armed (:slot ob)))
          entries (filter #(= :timer-entry (:event %)) (:events after))]
      (vec
       (concat
        (when (not= (if fires? 1 0) (count entries))
          [{:timer n :unexpected-entries (vec entries) :expected-entry? (boolean fires?)}])
        (for [ev entries
              :when (or (not= (select-keys action [:n :frame :variant :value])
                              (select-keys ev [:n :frame :variant :value]))
                        (not= [w r o] [(:world ev) (:r ev) (:o ev)])
                        (and (= :ok (:variant ev)) (not= (:value old) (:value ev))))]
          {:timer n :forged-entry ev})
        (for [[id row] (get-in before [:env :native]) :when (cleanup/timer-resource? row)
              :let [current (get-in after [:env :native id])
                    returned? (and (= :timer-return t) (= id n))
                    entered? (and fires? (= id n))
                    expected (cond entered? #{(:frame action)} returned? #{} :else (:frames row))]
              :when (or (not= expected (get current :frames #{}))
                        (and current (not= (:owner row) (:owner current)))
                        (and (:retired? row) current (not= (:anchor row) (:anchor current)))
                        (and (seq (:frames row)) (not returned?) (nil? current)))]
          {:timer id :physical-or-owner-conservation {:before row :after current :action action}})
        (for [[id row] (get-in before [:env :native]) :when (cleanup/timer-resource? row)
              :let [current (get-in after [:env :native id])]
              :when (and (nil? current)
                         (or (and (= :pending (:install row))
                                  (not (and (= id n) (= :timer-install-result t))))
                             (and (#{:present :release-pending :release-claimed} (:handle row))
                                  (not (and (= id n) (= :timer-handle-release t) (= :returned (:phase action)))))))]
          {:timer id :lost-install-or-disposal-receipt row})
        (for [[id row] (get-in after [:env :native])
              :when (and (cleanup/timer-resource? row) (nil? (get-in before [:env :native id]))
                         (not (and (= :timer-register t) (= id n) (= :pending (:install row))
                                   (= :armed (:phase row)) (empty? (:frames row)))))]
          {:timer id :unregistered-resource row}))))))

(defn- released-physical? [s w]
  (or (some #(and (= w (:world %)) (:run %)) (vals (get-in s [:env :threads])))
      (some #(and (= w (first (:owner %))) (not= :joined (:state %))) (vals (get-in s [:env :native])))))

(defn- obsolete-release-attempt? [s w packet]
  ;; Independent oracle: identify the allocation from the accepted envelope,
  ;; then inspect every surviving cohort rather than trusting its original key.
  (let [event (:event packet)
        [kind e] (cond (contains? event :deferred-assignment) [:deferred (:deferred-assignment event)]
                       (contains? event :mailbox-post) [:mailbox (:mailbox-post event)])
        allocation (:allocation event) live (get-in s [:worlds w :entities e])]
    (and (= w (:w packet)) kind (contains? event :allocation)
         (= :released (:status (m/wr s w)))
         (not (and (:owner live) (= [kind allocation] [(:kind live) (:allocation live)])))
         (empty? (for [[[world _ resource] cell] (get-in s [:env :cleanup-cells])
                       :when (and (= [w e kind allocation] [world resource (:kind cell) (:allocation cell)])
                                  (seq (:holders cell)))] cell)))))

(defn cleanup-terminal-proof? [s {:keys [target-world cap op]}]
  (let [leaf (get (m/all-caps s) cap) record (get (m/all-records s) op)
        terminal-kind ({:discard :discarded :merge :merged} (:kind record))]
    (and terminal-kind (= terminal-kind (:disposition leaf))
         (= target-world (:world leaf)) (= cap (:cap record))
         (= op (:op leaf) (:op record)) (= (:kind leaf) (:kind record))
         (true? (:effects-released? record))
         (every? #(= :done (:status %)) (:steps record)))))

(defn composed-ready-proof
  "Independent backward badness propagation; no production readiness calls."
  [s graph]
  (let [worlds (set (concat (keys (:worlds s)) (keys graph)
                            (map :target-world (mapcat vals (vals graph)))))
        bad (set (filter (fn [w]
                           (or (not= :released (get-in s [:worlds w :status]))
                               (released-physical? s w)
                               (some #(not (cleanup-terminal-proof? s %)) (vals (get graph w))))) worlds))]
    (loop [bad bad]
      (let [next (into bad (for [[source rows] graph
                                 :when (some #(contains? bad (:target-world %)) (vals rows))] source))]
        (if (= bad next) (set/difference worlds bad) (recur next))))))

(declare cleanup-proof-graph cleanup-target-errors)

(defn release-errors [s]
  (vec
   (concat (cleanup-target-errors s)
           (for [[w row] (get-in s [:env :releases])
                 :let [joined? (= :joined (:phase row)) physical? (boolean (released-physical? s w))]
                 :when (or (not= (:id row) [:world-release w])
                           (not= :released (:status (m/wr s w)))
                           (not (contains? row :reason))
                           (not (#{:releasing :joined} (:phase row)))
                           (not (and (integer? (:next-observer row)) (not (neg? (:next-observer row)))))
                           (not= joined? (contains? row :result)) (and joined? (some? (:result row)))
                           (not= joined? (contains? (composed-ready-proof s (get-in s [:env :cleanup-targets])) w))
                           (and joined? (some #(obsolete-release-attempt? s w %) (get-in s [:env :outside])))
                           (not= (set (keys row)) (cond-> #{:id :reason :phase :next-observer :observers} joined? (conj :result)))
                           (some (fn [[id observer]]
                                   (or (not (and (vector? id) (= 2 (count id)) (= (:id row) (first id))
                                                 (integer? (second id)) (<= 1 (second id) (:next-observer row))))
                                       (not= {:state (if joined? :ready :waiting)} observer))) (:observers row)))]
             {:w w :release row :physical? physical?}))))

(defn release-edge-errors [{:keys [before action after refusal observation]}]
  (when (and (not refusal) (not observation) (not (process-loss? action)))
    (let [t (:t action) w (:w action) old (get-in before [:env :releases w])
          deliveries (filter #(= :release-delivery (:event %)) (:events after))
          joins (filter #(= :release-joined (:event %)) (:events after))
          notifying? (= :release-notify t)
          expected-delivery (when notifying?
                              {:event :release-delivery :world w :release (:release action)
                               :observer (:observer action) :variant :ok :value nil})
          first-request? (and (= :release-request t) (nil? old))
          newly-joined (set (for [[world row] (get-in after [:env :releases])
                                  :when (and (= :joined (:phase row))
                                             (not= :joined (get-in before [:env :releases world :phase])))] world))]
      (vec
       (concat
        (when (not= (if notifying? [expected-delivery] []) (vec deliveries))
          [{:unexpected-release-deliveries (vec deliveries) :action action}])
        (for [[world row] (get-in before [:env :releases])
              :let [current (get-in after [:env :releases world])
                    observe? (and (= :release-observe t) (= world w))
                    removed (set/difference (set (keys (:observers row))) (set (keys (:observers current))))
                    added (set/difference (set (keys (:observers current))) (set (keys (:observers row))))]
              :when (or (nil? current) (not= (select-keys row [:id :reason]) (select-keys current [:id :reason]))
                        (not= (+ (:next-observer row) (if observe? 1 0)) (:next-observer current))
                        (not= (if observe? #{(:observer action)} #{}) added)
                        (and (seq removed) (not (and (= world w) (#{:release-detach :release-notify} t)
                                                     (= #{(:observer action)} removed))))
                        (and (= :joined (:phase row)) (not= :joined (:phase current)))
                        (not= (= :joined (:phase current))
                              (contains? (composed-ready-proof after (cleanup-proof-graph {:before before :action action :after after})) world)))]
          {:w world :release-conservation {:before row :after current :action action}})
        (for [[world row] (get-in after [:env :releases])
              :when (nil? (get-in before [:env :releases world]))
              :when (or (not (and first-request? (= world w) (= (:release action) (:id row))))
                        (not= (get action :reason :org.replikativ.spindel.engine.protocols/released) (:reason row))
                        (not= 0 (:next-observer row)) (seq (:observers row)))]
          {:w world :unissued-release row})
        (let [expected (set (for [[world row] (get-in after [:env :releases])
                                  :when (and (= :joined (:phase row))
                                             (not= :joined (get-in before [:env :releases world :phase])))]
                              {:event :release-joined :world world :release (:id row)}))]
          (when (or (not= expected (set joins)) (not= (count expected) (count joins)))
            [{:expected-release-joins expected :actual (vec joins)}]))
        (when (and (seq newly-joined) (not first-request?))
          (let [outside (get-in before [:env :outside])
                consumed (when (and (#{:deferred-assign :mailbox-post} t)
                                    (empty? (:queue (m/wr before w))))
                           (first (filter #(= w (:w %)) outside)))
                ;; Only the authenticated front attempt can be processed by
                ;; this action. All other prior packets survive unless the
                ;; independently checked post-return allocation is now dead.
                expected (vec (remove (fn [packet]
                                        (or (and consumed (= consumed packet))
                                            (some #(and (not (released-physical? after %))
                                                        (obsolete-release-attempt? after % packet)) newly-joined)))
                                      outside))]
            (when (not= expected (get-in after [:env :outside]))
              [{:release-outside-conservation {:before outside :expected expected
                                               :actual (get-in after [:env :outside]) :action action}}])))
        (when first-request?
          (let [reason (get action :reason :org.replikativ.spindel.engine.protocols/released)]
            (concat
             (for [[id row] (get-in after [:env :native])
                   :when (and (cleanup/mailbox-callback? row) (= :error (:variant row))
                              (= w (first (:owner row))) (nil? (get-in before [:env :native id]))
                              (not= reason (:delivery row)))]
               {:receipt id :lost-release-reason {:expected reason :actual (:delivery row)}})
             (for [event (:events after) :when (and (= :host-delivery (:event event)) (= w (:world event))
                                                    (not= reason (:value event)))]
               {:host-result-lost-release-reason event})))))))))

(defn custody-owner-chain
  "Read the pre-edge forest directly; no ownership/claim implementation helper."
  [state w owner]
  (let [world (get-in state [:worlds w])]
    (loop [id owner seen #{} result []]
      (if (or (nil? id) (contains? seen id)) result
          (let [rr (get-in world [:runs id]) scope (get-in world [:scopes id])
                kind (cond (= id (:root world)) :root scope :scope :else :run)]
            (recur (if rr (:owner rr) (:parent scope)) (conj seen id)
                   (conj result [:execution-owner w kind id])))))))

(defn custody-owner-retired? [before after holder]
  (when (= :execution-owner (first holder))
    (let [[_ w kind id] holder old (get-in before [:worlds w]) next (get-in after [:worlds w])]
      (and old (not= :released (:status old))
           (if (= :run kind)
             (let [row (get-in old [:runs id]) actual (get-in next [:runs id])]
               (and row (not= :unwinding (:status row))
                    (or (nil? actual) (= :unwinding (:status actual)) (= :released (:status next)))))
             (and (= :open (get-in old [:scopes id :status]))
                  (or (not= :open (get-in next [:scopes id :status])) (= :released (:status next)))))))))

(defn custody-admitted? [state holder]
  (when (and (vector? holder) (= :execution-owner (first holder)))
    (let [[_ w kind id] holder world (get-in state [:worlds w]) row (get-in world [:runs id])
          generations (for [[r rr] (:runs world) :when (= (:spin row) (:spin rr))] (second r))
          reactive? (some (fn [[_ ob]] (and (= [:run w id] (:creditor ob)) (:standing? ob)
                                            (#{:track :await-reactive} (:kind ob)))) (:obligations world))]
      (and world (not= :released (:status world))
           (if (= kind :run)
             (and row (= (second id) (reduce max -1 generations))
                  (or (#{:running :parked} (:status row)) (and (= :completed (:status row)) reactive?)))
             (= :open (get-in world [:scopes id :status])))))))

(defn custody-actor? [state holder]
  (and (vector? holder)
       (case (first holder)
         :execution-owner (custody-admitted? state holder)
         :external (contains? (get-in state [:env :principals] #{}) holder)
         :cleanup (contains? (get-in state [:custody :claims]) (second holder))
         :recovery (and (:restarted? state) (= holder [:recovery :durable (:recovery-epoch state)]))
         false)))

(defn custody-destination-acquisition [state holder acceptance]
  (if (= :external (first holder))
    (when (contains? (get-in state [:env :principals] #{}) holder) {:acquisition nil})
    (when (custody-admitted? state holder)
      (let [[_ w kind id] holder world (get-in state [:worlds w]) row (get-in world [:runs id])]
        (when (and (= :live (:status world)) (= :open (:admission world)))
          (if (not= :run kind) {:acquisition nil}
              (if (not= :running (:status row)) {:acquisition :exact-run}
                  (let [{:keys [th order]} acceptance frame (get-in state [:env :threads th])]
                    (when (and (= w (:world frame)) (= id (:run frame)) (:executing? frame)
                               (not (:retired? frame)) (nil? (:cleanup-ticket frame))
                               (integer? order) (<= 0 order)) {:acquisition order})))))))))

(defn custody-loss-consistent? [state]
  (and (false? (:process-live? state)) (false? (:restarted? state))
       (not-any? seq (map #(get state %) [:worlds :cuts :registry :caps :records]))
       (not-any? seq (vals (:custody state)))
       (= (:env state) {:handles {} :threads {} :native {} :waiters {} :gc [] :outside [] :principals #{}})))

(defn custody-terminal-envelope? [state w event]
  (let [cap (get (m/all-caps state) (:cap event)) record (get (m/all-records state) (:op event))]
    (and (#{:merged :discarded} (:disposition cap)) (= w (:world cap))
         (= [:cleanup (:custody-dispatch event)] (:holder cap))
         (= (:op event) (:op cap)) (= (:cap event) (:cap record)))))

(defn custody-effective-delivery [before action]
  (loop [action action]
    (let [thread (get-in before [:env :threads (get action :th :host)])
          action (cond-> action
                   (or (nil? (:w action)) (and (:th action) (:run thread))) (assoc :w (:world thread)))]
      (case (:t action)
        :t21 (recur (or (:body action)
                        {:t :queued :w (first (get-in before [:cuts (:c action) :participants :worlds]))}))
        :queued (let [event (first (get-in before [:worlds (:w action) :queue]))]
                  (cond (:action event) (recur (:action event))
                        (:completion event) (assoc event :t :t08 :w (:w action) :e (:completion event))
                        :else action))
        action))))

(defn custody-reentry-triggers [before action]
  (let [action (custody-effective-delivery before action) w (:w action)]
    (case (:t action)
      :t09 [{:world w :spin (:e action) :order (get action :order -1)}]
      :t08 (let [debtor [:entity (or (:debtor-world action) w) (:e action)]
                 pending (queued-events before w)]
             (vec (for [[o ob] (get-in before [:worlds w :obligations])
                        :let [[kind _ r] (:creditor ob)
                              cancelling? (and (not= w (second debtor)) (some #(= o (:cancelled %)) pending))]
                        :when (and (= :run kind) (:standing? ob) (= :consumed (:slot ob))
                                   (= debtor (:debtor ob)) (not cancelling?)
                                   (not= :inherited (get-in before [:worlds w :runs r :status])))]
                    {:world w :spin (first r) :order (:order ob)})))
      [])))

(defn custody-forest-ref [forest id]
  [:execution-owner (:world forest)
   (cond (= id (:root forest)) :root (contains? (:scopes forest) id) :scope :else :run) id])

(defn custody-forest-anchor [forest owner]
  (loop [id owner seen #{} chain []]
    (if (or (nil? id) (contains? seen id)) chain
        (recur (if-let [run (get-in forest [:runs id])] (:owner run)
                       (get-in forest [:scopes id :parent]))
               (conj seen id) (conj chain (custody-forest-ref forest id))))))

(defn custody-forest-retire
  "Freeze the effective mixed ancestry before deleting any of this closure."
  [forest roots]
  (let [owners (loop [owners (set roots)]
                 (let [owned-spins (set (for [[e row] (:entities forest)
                                              :when (and (= :spin (:kind row)) (contains? owners (:owner row)))] e))
                       children (concat
                                 (for [[id row] (:scopes forest) :when (contains? owners (:parent row))] id)
                                 (for [[r row] (:runs forest)
                                       :when (and (not= :unwinding (:status row))
                                                  (or (contains? owners (:owner row)) (contains? owned-spins (:spin row))))] r))
                       next (into owners children)]
                   (if (= owners next) owners (recur next))))
        anchors (into {} (for [id owners :when (or (contains? (:runs forest) id) (contains? (:scopes forest) id))]
                           [(custody-forest-ref forest id) (custody-forest-anchor forest id)]))]
    [(-> forest
         (update :runs #(into {} (for [[r row] % :when (not (contains? owners r))]
                                   [r (cond-> (update row :ancestors (fn [ids] (set/difference (or ids #{}) owners)))
                                        (contains? owners (:pred row)) (assoc :pred nil))])))
         (update :scopes #(apply dissoc % owners))
         (update :entities #(into {} (for [[e row] %]
                                       [e (cond-> row (contains? owners (:owner row)) (assoc :owner nil)
                                                  (contains? owners (:creator row)) (assoc :creator nil))]))))
     anchors]))

(defn custody-forest-adopt-entity [forest entity old-owner new-owner creation?]
  (let [creator (get-in forest [:entities entity :creator])]
    (-> forest
        (assoc-in [:entities entity :owner] new-owner)
        (cond-> creator (assoc-in [:entities entity :creator] new-owner)
                creation? (update-in [:runs new-owner :creations] (fnil conj #{}) entity)
                creation? (update-in [:runs old-owner :creations] disj entity))
        (update :runs #(into {} (for [[r row] %]
                                  [r (if (and (= entity (:spin row)) (= old-owner (:owner row)))
                                       (assoc row :owner new-owner) row)]))))))

(defn custody-reentry-forest
  "Ordered independent owner projection across ALL Spins in one delivery.
   No cap result, reverse index or model transition is used to construct it."
  [before action after]
  (let [triggers (custody-reentry-triggers before action) w (:world (first triggers))
        relevant? (some (fn [[_ c]]
                          (let [[tag world kind id] (:holder c)]
                            (and (not (m/terminal (:disposition c))) (= :execution-owner tag) (= w world)
                                 (or (= :run kind)
                                     (some #(= :run (nth % 2)) (custody-owner-chain before w id)))))) (m/all-caps before))]
    (when (and (seq triggers) relevant?)
      (let [world (get-in before [:worlds w]) effective (custody-effective-delivery before action)
            allocation (if (contains? action :fresh-runs) action effective)
            explicit? (contains? allocation :fresh-runs)
            initial {:world w :root (:root world) :runs (:runs world) :scopes (:scopes world)
                     :entities (:entities world) :obligations (:obligations world)
                     :clocks (into {} (for [[[world spin] n] (:generation-clock before) :when (= world w)] [spin n]))
                     :max-generation (reduce max 0 (vals (:generation-clock before)))
                     :steps [] :errors []}
            forest
            (reduce
             (fn [forest [i {:keys [spin order]}]]
               (let [old (last (sort-by second (for [[r row] (:runs forest) :when (= spin (:spin row))] r)))
                     row (get-in forest [:runs old])
                     stale (for [[r rr] (:runs forest) :when (and (= spin (:spin rr)) (= :stale (:status rr)))] r)
                     [forest stale-anchors] (custody-forest-retire forest stale)
                     inherited (for [[r rr] (:runs forest) :when (and (= spin (:spin rr)) (= :inherited (:status rr)))] r)
                     [forest inherited-anchors] (custody-forest-retire forest inherited)
                     retired (merge stale-anchors inherited-anchors)
                     previous (get-in forest [:runs old])
                     pred (last (sort-by second (for [[r rr] (:runs forest) :when (= spin (:spin rr))] r)))
                     base (max (or (second pred) 0) (get-in forest [:clocks spin] 0))
                     declaration (when explicit? (nth (:fresh-runs allocation) i nil))
                     stamp (if explicit? (nth declaration 2 nil) (inc base))
                     valid-stamp? (and (integer? stamp) (> stamp base)
                                       (or (not explicit?) (and (= w (first declaration)) (= spin (second declaration))
                                                                (> stamp (:max-generation forest)))))
                     stamp (if valid-stamp? stamp (inc base)) fresh [spin stamp]
                     forest (-> forest
                                (assoc-in [:clocks spin] stamp)
                                (update :max-generation max stamp)
                                (assoc-in [:runs fresh] {:spin spin :owner (:owner row) :status :running :creations #{}
                                                         :ancestors (cond-> (get-in forest [:runs pred :ancestors] #{}) pred (conj pred))})
                                (cond-> (#{:running :parked} (:status previous)) (assoc-in [:runs old :status] :stale))
                                (cond-> (not valid-stamp?) (update :errors conj {:invalid-reentry-allocation {:declaration declaration :spin spin}})))
                     ;; Prefix reactive calls can adopt a portable entity even
                     ;; when it is absent from the predecessor's creations.
                     forest (reduce (fn [forest [o ob]]
                                      (if (not= [:run w old] (:creditor ob)) forest
                                          (if (and previous
                                                   (or (and (= :track (:kind ob)) (<= (:order ob) order))
                                                       (and (= :await-reactive (:kind ob)) (:standing? ob)
                                                            (= :consumed (:slot ob)) (< (:order ob) order))))
                                            (let [[kind dw entity] (:debtor ob)
                                                  owner (get-in forest [:entities entity :owner])
                                                  adopt? (and (= :await-reactive (:kind ob)) (= :entity kind) (= dw w)
                                                              (contains? (get-in forest [:runs fresh :ancestors]) owner))]
                                              (cond-> (assoc-in forest [:obligations o :creditor] [:run w fresh])
                                                adopt? (custody-forest-adopt-entity entity owner fresh
                                                                                    (= owner (get-in forest [:entities entity :creator])))))
                                            (if (#{:running :parked} (:status previous))
                                              (update forest :obligations dissoc o) forest)))) forest (:obligations forest))
                     forest (update forest :scopes
                                    #(into {} (for [[id scope] %]
                                                [id (if (and (= old (:parent scope)) (< (get scope :order 0) order))
                                                      (assoc scope :parent fresh) scope)])))
                     prefix (filter #(< (get-in forest [:entities % :order] 0) order) (:creations previous))
                     forest (reduce #(custody-forest-adopt-entity %1 %2 old fresh true) forest prefix)]
                 (update forest :steps conj {:spin spin :order order :old old :new fresh :previous? (some? previous)
                                             :retired retired}))) initial (map-indexed vector triggers))
            expected (mapv (fn [{:keys [spin new]}] [spin new]) (:steps forest))
            entries (mapv #(vector (:e %) (:r %)) (filter #(and (= :body-entry (:event %)) (= w (:world %))) (:events after)))
            touched (set (map :spin triggers))
            valid? (and (= expected entries)
                        (or (not explicit?) (= (count triggers) (count (:fresh-runs allocation))))
                        (every? #(= (get-in forest [:clocks %]) (get-in after [:generation-clock [w %]])) touched))]
        (cond-> forest
          (not valid?) (update :errors conj {:invalid-reentry-evidence {:expected expected :entries entries
                                                                        :expected-clocks (select-keys (:clocks forest) touched)}}))))))

(defn custody-reentry-path [before action after c forest]
  (let [[tag w kind id :as source] (:holder c)]
    (when (and forest (= :execution-owner tag) (= w (:world forest)))
      (reduce (fn [{:keys [holder closed?] :as path} {:keys [old new order previous? retired]}]
                (cond
                  closed? path
                  (contains? retired holder) (assoc path :closed? true :origin holder :anchor (get retired holder))
                  (and (= :run (nth holder 2)) (= old (nth holder 3)) previous?
                       (integer? (:holder-acquisition c)) (< (:holder-acquisition c) order))
                  (assoc path :holder [:execution-owner w :run new])
                  :else path)) {:holder source :closed? false} (:steps forest)))))

(defn custody-errors
  "Independent live-cap census; reverse membership is never its own oracle."
  [s]
  (let [caps (m/all-caps s) live (remove #(m/terminal (:disposition (val %))) caps)
        process? (not= false (:process-live? s))
        expected (if process? (reduce (fn [index [k c]] (update index (:holder c) (fnil conj #{}) k)) {} live) {})
        claims (get-in s [:custody :claims])]
    (vec
     (concat
      (when-let [duplicate (seq (set/intersection (set (keys (:caps s))) (set (keys (get-in s [:durable :caps])))))]
        [{:duplicate-cap-storage (set duplicate)}])
      (when-let [duplicate (seq (set/intersection (set (keys (:records s))) (set (keys (get-in s [:durable :records])))))]
        [{:duplicate-operation-storage (set duplicate)}])
      (when-not (boolean? (:process-live? s)) [{:invalid-process-state (:process-live? s)}])
      (when (and (false? (:process-live? s)) (not (custody-loss-consistent? s)))
        [{:inconsistent-process-loss true}])
      (let [operations (concat
                        (for [[k c] caps :when (some? (:op c))] [(:op c) k])
                        (for [[op record] (m/all-records s)] [op (:cap record)])
                        (for [[_ claim] claims] [(:settlement-op claim) (:cap claim)]))]
        (for [[op owners] (group-by first operations)
              :when (or (nil? op) (> (count (set (map second owners))) 1))]
          {:operation-reservation-collision {:op op :owners (set (map second owners))}}))
      (when (or (not (integer? (:next-claim s))) (neg? (:next-claim s))
                (not (integer? (:recovery-epoch s))) (neg? (:recovery-epoch s)))
        [{:invalid-custody-allocator [(:next-claim s) (:recovery-epoch s)]}])
      (for [id (concat (keys claims)
                       (for [[_ c] caps :when (and (vector? (:holder c)) (= :cleanup (first (:holder c))))] (second (:holder c))))
            :when (not (and (vector? id) (= 2 (count id)) (= :custody-claim (first id))
                            (integer? (second id)) (<= 0 (second id)) (integer? (:next-claim s)) (< (second id) (:next-claim s))))]
        {:invalid-claim-identity id})
      (when (not= expected (get-in s [:custody :by-holder]))
        [{:index-conservation {:expected expected :actual (get-in s [:custody :by-holder])}}])
      (for [[k c] caps :when (not (m/holder-ref? (:holder c)))] {:k k :malformed-holder (:holder c)})
      (for [[k c] live :when process? :let [holder (:holder c)]
            :when (case (when (vector? holder) (first holder))
                    :execution-owner (let [[_ w kind id] holder]
                                       (or (nil? (m/wr s w)) (= :released (:status (m/wr s w)))
                                           (if (= :run kind)
                                             (or (nil? (m/run s w id)) (= :unwinding (:status (m/run s w id))))
                                             (not= :open (get-in s [:worlds w :scopes id :status])))))
                    :external (not (contains? (get-in s [:env :principals] #{}) holder))
                    :cleanup (not= k (:cap (get claims (second holder))))
                    :recovery (not= holder [:recovery :durable (:recovery-epoch s)])
                    true)]
        {:k k :inactive-custodian holder})
      (for [[k c] live :when (and (vector? (:holder c)) (= :execution-owner (first (:holder c))) (= :run (nth (:holder c) 2 nil))
                                  (not (or (= :exact-run (:holder-acquisition c))
                                           (and (integer? (:holder-acquisition c)) (not (neg? (:holder-acquisition c)))))))]
        {:k k :invalid-acquisition (:holder-acquisition c)})
      (for [[id claim] claims :let [c (get caps (:cap claim))]
            :when (or (nil? c) (m/terminal (:disposition c))
                      (not= [:cleanup id] (:holder c)) (not= [:cleanup id] (:holder claim))
                      (not= (:world c) (:target-world claim))
                      (not (#{:dispatch-pending :active} (:phase claim)))
                      (and (not= :open (:disposition c))
                           (or (not= (:op c) (:settlement-op claim)) (not= (:kind c) (:kind claim)))))]
        {:claim id :invalid-claim claim :cap c})
      (for [[id claim] claims :when (= :dispatch-pending (:phase claim))
            :let [matching (filter #(and (= id (:custody-dispatch %)) (= (:cap claim) (:cap %))
                                         (= (:settlement-op claim) (:op %)))
                                   (queued-events s (:target-world claim)))]
            :when (not= 1 (count matching))]
        {:claim id :pending-dispatch-count (count matching)})
      (for [[w world] (:worlds s) event (queued-events s w) :when (:custody-dispatch event)
            :let [claim (get claims (:custody-dispatch event))]
            :when (if claim
                    (or (not= w (:target-world claim)) (not= (:cap event) (:cap claim))
                        (not= (:op event) (:settlement-op claim)))
                    (not (custody-terminal-envelope? s w event)))]
        {:w w :uncommitted-envelope event})))))

(defn custody-operation-reserved? [state op exempt]
  (or (nil? op) (contains? (m/all-records state) op)
      (some #(= op (:op %)) (vals (m/all-caps state)))
      (some (fn [[id claim]] (and (not= id exempt) (= op (:settlement-op claim))))
            (get-in state [:custody :claims]))))

(defn custody-edge-errors [{:keys [before action after refusal]}]
  (when-not refusal
    (let [outer-action action
          action (custody-effective-delivery before action)
          t (:t action) k (:k action) old (m/cap before k) new (m/cap after k)
          before-caps (m/all-caps before) after-caps (m/all-caps after)
          restart? (and (= :t31 t) (= :restart (:phase action)))
          forest (when (not= :t31 t) (custody-reentry-forest before outer-action after))]
      (vec
       (concat
        (:errors forest)
        (when (and (not (#{:t31 :join} t))
                   (or (not (true? (:process-live? before)))
                       (not= (select-keys before [:process-live? :restarted? :recovery-epoch])
                             (select-keys after [:process-live? :restarted? :recovery-epoch]))))
          [{:unavailable-process-mutation action}])
        (when (#{:t26 :t32 :t33} t)
          (let [caller (:caller action)
                claim-id (when (and (= :t26 t) (= :cleanup (first caller))) (second caller))
                claim (get-in before [:custody :claims claim-id])
                valid-claim? (and (= caller (:holder old)) (= k (:cap claim))
                                  (= (:op action) (:settlement-op claim)) (= (get action :kind :merge) (:kind claim)))]
            (concat
             (when (or (not= caller (:holder old)) (not (custody-actor? before caller))
                       (and claim-id (not valid-claim?))) [{:unauthenticated-operation action}])
             (when (custody-operation-reserved? before (:op action) (when valid-claim? claim-id))
               [{:reused-operation (:op action)}]))))
        (when (#{:t32 :t33} t)
          (let [successors (if (= :t32 t) [(:successor action)] (mapv :k (:successors action)))
                leaves (map #(m/cap after %) successors)
                destination (when (= :t32 t) (custody-destination-acquisition before (:holder action) (:acceptance action)))]
            (concat
             (when (or (not= (:caller action) (:holder old)) (not (custody-actor? before (:caller action)))
                       (not (#{:execution-owner :external} (first (:caller action))))
                       (and (= :t32 t) (or (not= (:holder action) (:acceptor action)) (nil? destination))))
               [{:unauthenticated-consumption action}])
             (when (or (not= (set successors) (set/difference (set (keys after-caps)) (set (keys before-caps))))
                       (not= (if (= :t32 t) :transferred :partitioned) (:disposition new))
                       (not= successors (:successors new)))
               [{:bad-consumption {:old k :successors successors :action action}}])
             (when (or (not= (:scope old) (apply set/union #{} (map :scope leaves)))
                       (not= (count (:scope old)) (reduce + 0 (map (comp count :scope) leaves)))
                       (some #(not= (:world old) (:world %)) leaves) (some #(not= k (:pred %)) leaves))
               [{:lost-authority {:k k :leaves leaves}}])
             (for [[id leaf] (map vector successors leaves)
                   :let [expected-holder (if (= :t32 t) (:holder action) (:holder old))
                         expected-acquisition (if (= :t32 t) (:acquisition destination) (:holder-acquisition old))
                         expected-bases (if (= :t32 t) (:bases old) (select-keys (:bases old) (:scope leaf)))]
                   :when (or (not= expected-holder (:holder leaf))
                             (not= expected-acquisition (:holder-acquisition leaf)) (not= expected-bases (:bases leaf)))]
               {:bad-successor-custody {:k id :expected-holder expected-holder :expected-acquisition expected-acquisition
                                        :expected-bases expected-bases :actual leaf}})
             (for [[id c] before-caps :when (and (not= id k) (not= c (get after-caps id)))] {:unrelated-cap-mutated id}))))
        ;; Read BEFORE caps and owner forests, never the stored reverse bucket.
        (when (not= :t31 t)
          (mapcat
           (fn [[id c]]
             (let [next (get after-caps id) source (:holder c)
                   path (when-not (m/terminal (:disposition c)) (custody-reentry-path before outer-action after c forest))
                   retired? (or (:closed? path) (and (= source (:holder path source))
                                                     (custody-owner-retired? before after source)))
                   close-source (or (:origin path) source)
                   close-anchor (or (:anchor path)
                                    (when (= :execution-owner (first source))
                                      (custody-owner-chain before (second source) (nth source 3))))
                   terminalizing? (and (= :t29 t) (= id (:cap (m/record before (:op action)))))
                   rollback? (and (not (:published? c)) (nil? next)
                                  (some (fn [[cut-id cut]]
                                          (and (= (:world c) (:child cut))
                                               (#{:fenced :ready :captured :attached} (:phase cut))
                                               (= :failed (get-in after [:cuts cut-id :phase])))) (:cuts before)))
                   captures (for [[claim-id claim] (get-in after [:custody :claims]) :when (= id (:cap claim))] [claim-id claim])]
               (cond
                 (m/terminal (:disposition c))
                 (when (not= c next) [{:terminal-history-changed id}])
                 rollback? []
                 terminalizing? []
                 retired?
                 (let [[claim-id claim] (first captures)
                       sealing? (and (= :t26 t) (= id k))
                       expected-op (if sealing? (:op action) (:op c))
                       expected-kind (if sealing? (get action :kind :merge) (:kind c))]
                   (concat
                    (when (or (not= 1 (count captures)) (not= [:cleanup claim-id] (:holder next))
                              (not= close-source (:origin claim)) (some? (:holder-acquisition next))
                              (not= (:world c) (:target-world claim))
                              (not= (select-keys c [:world :scope :bases]) (select-keys next [:world :scope :bases]))
                              (not= (if sealing? :sealed (:disposition c)) (:disposition next))
                              (not= expected-op (:op next)) (not= expected-kind (:kind next))
                              (not= close-anchor (:anchor claim)))
                      [{:lost-close-custody {:k id :source source :claims (vec captures) :actual next}}])
                    (when (if (or sealing? (not= :open (:disposition c)))
                            (or (not= expected-op (:settlement-op claim)) (not= expected-kind (:kind claim)))
                            (not= :discard (:kind claim)))
                      [{:changed-close-disposition {:k id :claim claim}}])
                    (when (and (some? expected-op) (not= (m/record before expected-op) (m/record after expected-op)))
                      [{:changed-close-record id}])))
                 path
                 (when (or (not= (:holder path) (:holder next)) (not= (dissoc c :holder) (dissoc next :holder)))
                   [{:wrong-prefix-custody {:k id :expected (:holder path) :actual (:holder next)}}])
                 :else
                 (when (or (not= source (:holder next)) (not= (:holder-acquisition c) (:holder-acquisition next))
                           (not= (:bases c) (:bases next)))
                   [{:unrelated-custody-changed {:k id :before c :after next}}])))) before-caps))
        (when (= :t31 t)
          (concat
           (when (and (not restart?)
                      (or (not (custody-loss-consistent? after))
                          (not= (:recovery-epoch before) (:recovery-epoch after))
                          (not= (get-in before [:durable :caps]) (get-in after [:durable :caps]))))
             [{:invalid-process-loss-edge true}])
           (when (and restart? (or (not (custody-loss-consistent? before))
                                   (not (true? (:process-live? after)))
                                   (not= (inc (:recovery-epoch before)) (:recovery-epoch after))))
             [{:unearned-recovery-takeover true}])
           (when restart?
             (for [[id c] (get-in before [:durable :caps]) :when (not (m/terminal (:disposition c)))
                   :let [next (get after-caps id)]
                   :when (or (not= [:recovery :durable (:recovery-epoch after)] (:holder next))
                             (some? (:holder-acquisition next)) (not= (:bases c) (:bases next))
                             (and (not= :open (:disposition c))
                                  (or (not= (:op c) (:op next)) (not= (:kind c) (:kind next)))))]
               {:missing-recovery-custody id}))
           (for [[id rec] (get-in before [:durable :records])
                 :let [expected (if (:successors rec)
                                  (update rec :successors
                                          #(mapv (fn [desc]
                                                   (if (and (not (:durable? desc))
                                                            (or (not restart?) (nil? (get after-caps (:k desc)))))
                                                     (assoc desc :disposition :discarded :vanished? true) desc)) %)) rec)]
                 :when (not= expected (m/record after id))]
             {:recovery-record-rewritten id}))))))))

(def predicates
  [[:L1 l01] [:L2 l02] [:L3 l03] [:L4 l04] [:L5 l05] [:L6 l06] [:ScopeForest scope-errors]
   [:L7 l07] [:L8 l08] [:L9 l09] [:L10 l10] [:L11 l11] [:L12 l12]
   [:L13 l13] [:L14 l14] [:L15 l15] [:L16 l16] [:L17 l17] [:L18 l18]
   [:L19 l19] [:L20 l20] [:L21 l21] [:L22 l22] [:L23 l23] [:L24 l24] [:L25 l25] [:L26 l26] [:L27 cleanup/errors] [:L28 mailbox-errors] [:L29 timer-errors] [:L30 release-errors] [:Custody custody-errors]])
(defn check "§4.5 vector of violated L-ids with evidence." [s]
  (binding [m/*liveness-cache* (or m/*liveness-cache* (volatile! nil))]
    (vec (keep (fn [[id predicate]] (ev id (predicate s))) predicates))))

(defn writes [a b]
  (for [k (set/union (set (keys a)) (set (keys b))) :when (not= (get a k) (get b k))] k))
(def cut-transitions #{:t20 :t20q :t21 :t22 :t23 :t24 :t25})
(defn release-requests [s cut]
  (let [v (:child cut) evidence (:copy-evidence (first (vals (:basis cut))))
        rows (for [[o ob] (:obligations (m/wr s v))
                   :let [[kind dw e] (:debtor ob)]
                   :when (and (= :entity kind) (not= dw v) (= :run (first (:creditor ob)))
                              (= :inherited (:status (m/run s v (nth (:creditor ob) 2)))))]
               [dw e o ob])]
    (concat
     (for [[dw e o _] rows :when (= :pending-start (get-in evidence [o :phase]))]
       [dw {:start-for e :creditor-world v :o o}])
     (for [[dw members] (group-by first (filter #(= :admitted (get-in evidence [(nth % 2) :phase])) rows))]
       [dw {:join-bundle v :debtors (set (map second members))
            :members (into {} (for [[_ e o ob] members]
                                [o {:debtor e :source-world (:source-world ob) :source-o o}]))}]))))

(defn cut-footprint-errors [before action after]
  (let [c (:c action) old (get-in before [:cuts c]) cut (get-in after [:cuts c])
        participants (or (:participants old) (:participants action))
        worlds (:worlds participants) child (or (:child old) (:child cut))
        requester (first worlds)
        requests (when (= :t24 (:t action)) (release-requests before old))
        ingress (mapcat (fn [[w event :as request]]
                          (if (= :released (:status (m/wr before w)))
                            (for [o (if (:join-bundle event) (keys (:members event)) [(:o event)])]
                              [child {:cancelled o :value ::m/released}])
                            [request])) requests)
        expected-ingress
        (reduce (fn [acc [w event]]
                  (let [n (inc (get-in acc [:clocks w] (max (get-in before [:clocks w] 0)
                                                            (get-in before [:worlds w :seq] 0)
                                                                ;; Fresh entrypoint precedes request rejection.
                                                            (if (= w child)
                                                              (inc (max (get-in before [:clocks w] 0)
                                                                        (get-in before [:worlds w :seq] 0))) 0))))
                        held? (and (= :fenced (:admission (m/wr before w)))
                                   (m/cut-participant? before w) (not (worlds w)))]
                    (-> acc (assoc-in [:clocks w] n)
                        (update-in [(if held? :held :queues) w] (fnil conj []) (assoc event :seq n)))))
                {:queues (into {} (for [[w world] (:worlds before)]
                                    [w (into (vec (:queue world))
                                             (when (worlds w)
                                               (map :event (filter #(= w (:w %)) (get-in before [:env :outside])))))]))}
                ingress)
        expected-queues (:queues expected-ingress)
        ;; T24/T25 move held arrivals back to exactly their original queue.
        restored (fn [w] (into (vec (:queue (m/wr before w)))
                               (map :event (filter #(= w (:w %)) (get-in before [:env :outside])))))]
    (vec (concat
          (when (and (= :t24 (:t action))
                     (not= (merge {} (:clocks before) (:clocks expected-ingress)) (or (:clocks after) {})))
            [{:cut c :clocks-not-exact true}])
          (when (and (some #(= child (first %)) ingress)
                     (not= (get expected-queues child) (:queue (m/wr after child))))
            [{:cut c :child child :local-rejections-not-exact true}])
          (for [w worlds :when (and (not (#{:t20 :t20q} (:t action)))
                                    (not= :fenced (:admission (m/wr before w))))]
            {:cut c :w w :missing-fence true})
          (for [w (set/union (set (keys (:worlds before))) (set (keys (:worlds after))))
                :when (not= w child)
                :let [a (m/wr before w) b (m/wr after w)]
                field (writes a b)
                :when (not (or (and (worlds w) (= field :admission))
                               (and (worlds w) (= field :queue) (#{:t24 :t25} (:t action))
                                    (= (:queue b) (restored w)))
                               (and (= field :entities) (= w requester)
                                    (= (dissoc (:entities a) [:fork child]) (dissoc (:entities b) [:fork child])))
                               (and (= :t24 (:t action)) (= :queue field)
                                    (= (vec (:queue b)) (get expected-queues w (vec (:queue a)))))))]
            {:cut c :world w :field field})
          (for [w (set/union (:registry before) (:registry after))
                :when (and (not= w child) (not= (contains? (:registry before) w) (contains? (:registry after) w)))]
            {:cut c :registry w})
          (for [k (set/union (set (keys (m/all-caps before))) (set (keys (m/all-caps after))))
                :let [a (m/cap before k) b (m/cap after k)]
                :when (and (not= a b) (not= child (:world (or a b))))]
            {:cut c :cap k})
          (for [d (set/union (set (keys (:cuts before))) (set (keys (:cuts after))))
                :when (and (not= c d) (not= (get-in before [:cuts d]) (get-in after [:cuts d])))]
            {:cut c :other-cut d})
          (for [th (set/union (set (keys (get-in before [:env :threads])))
                              (set (keys (get-in after [:env :threads]))))
                :let [a (get-in before [:env :threads th]) b (get-in after [:env :threads th])
                      coordinator (or (:coordinator old) (:coordinator cut))]
                :when (not= (if (= th coordinator) (dissoc (or a {}) :excl-permits) a)
                            (if (= th coordinator) (dissoc (or b {}) :excl-permits) b))]
            {:cut c :thread th})
          (for [field [:native :waiters] :when (not= (get-in before [:env field]) (get-in after [:env field]))]
            {:cut c :env field})
          (for [tok (set/union (set (keys (get-in before [:env :handles])))
                               (set (keys (get-in after [:env :handles]))))
                :let [a (get-in before [:env :handles tok]) b (get-in after [:env :handles tok])]
                :when (not= (update a :touched disj child) (update b :touched disj child))]
            {:cut c :handle tok})
          (let [expected (if (#{:t24 :t25} (:t action))
                           (vec (remove #(worlds (:w %)) (get-in before [:env :outside])))
                           (get-in before [:env :outside]))
                expected (into expected (for [[w events] (:held expected-ingress) event events]
                                          {:w w :event event}))]
            (when (not= expected (get-in after [:env :outside])) [{:cut c :env :outside}]))
          (for [field [:records :durable]
                :let [a (if (= :durable field) (get-in before [:durable :records]) (:records before))
                      b (if (= :durable field) (get-in after [:durable :records]) (:records after))]
                :when (not= a b)] {:cut c :records field})))))

(declare edge-check)

(defn owner-release-errors
  "Rule 3 leaves a released entity runless, even when its run had another owner.
  Derive release from ownership changes, independently of run-exit audit events."
  [before after]
  (vec (for [[w e er] (entities before)
             :let [new (m/ent after w e)]
             :when (and (:owner er) (nil? (:owner new)))
             [r rr] (:runs (m/wr after w))
             :when (and (= e (:spin rr)) (not= :unwinding (:status rr)))]
         {:w w :e e :released-owner (:owner er) :surviving-run r :status (:status rr)})))

(defn- physical-ancestry [s w r]
  (loop [id r seen #{} result []]
    (cond
      (nil? id) (conj result w)
      (contains? seen id) result
      (= :unwinding (:status (m/run s w id))) (into result (:anchor (m/run s w id)))
      :else (recur (or (:owner (m/run s w id)) (get-in s [:worlds w :scopes id :parent]))
                   (conj seen id) (conj result id)))))

(defn- participant-ancestry [s w r participant]
  ;; Raw Mailbox callbacks are independent of the lifetime of their former
  ;; ordinary owner row. Other participants follow ordinary adoption until
  ;; retirement snapshots that ownership into the unwinding run's anchor.
  (if (cleanup/mailbox-callback? participant)
    (:anchor participant)
    (physical-ancestry s w r)))

(defn released-join-evidence-errors
  "Before world rows disappear, physical participants must retain the exact
   ancestry needed for run/scope/world joins. Do not derive it from their new
   stamped anchor, or a missing scope would become invisible to the oracle."
  [{:keys [before after refusal]}]
  (when-not refusal
    (vec
     (mapcat
      (fn [[w world]]
        (when (and (not= :released (:status (m/wr before w))) (= :released (:status world)))
          (concat
           (for [[th thread] (get-in before [:env :threads])
                 :let [r (:run thread) current (get-in after [:env :threads th])]
                 :when (and (= w (:world thread)) r)
                 :let [expected (physical-ancestry before w r)]
                 :when (or (not= [w r] [(:world current) (:run current)])
                           (not= expected (:anchor current)))]
             {:w w :thread th :r r :expected expected :actual current})
           (for [[n native] (get-in before [:env :native])
                 :let [[world r] (:owner native) current (get-in after [:env :native n])]
                 :when (and (= w world) (not= :joined (:state native))
                            (not (and (cleanup/timer-resource? native) (nil? current)
                                      (not= :pending (:install native)) (empty? (:frames native))
                                      (#{:none :released :failed} (:handle native)))))
                 :let [expected (participant-ancestry before w r native)]
                 :when (or (not= [w r] (:owner current)) (= :joined (:state current))
                           (not= expected (:anchor current)))]
             {:w w :native n :r r :expected expected :actual current}))))
      (:worlds after)))))

(defn join-errors [{:keys [before action after refusal observation]}]
  (when (= :join (:t action))
    (let [{:keys [w x timeout?]} action
          under? (fn [r rr]
                   (if (= :unwinding (:status rr)) (some #{x} (:anchor rr))
                       (loop [id r seen #{}]
                         (cond (= id x) true (nil? id) (= x w) (seen id) false
                               :else (recur (or (:owner (m/run before w id))
                                                (get-in before [:worlds w :scopes id :parent]))
                                            (conj seen id))))))
          busy (set (for [[r rr] (:runs (m/wr before w))
                          :when (and (#{:running :parked :unwinding} (:status rr)) (under? r rr))] r))
          physical-under? (fn [r participant]
                            (or (= x w) (= x r)
                                (some #{x} (if (= :released (:status (m/wr before w)))
                                             (:anchor participant)
                                             (participant-ancestry before w r participant)))))
          busy (into busy
                     (concat
                      (for [[_ thread] (get-in before [:env :threads])
                            :let [r (:run thread)]
                            :when (and r (= w (:world thread)) (physical-under? r thread))] r)
                      (for [[_ native] (get-in before [:env :native])
                            :let [[world r] (:owner native)]
                            :when (and (= w world) (not= :joined (:state native))
                                       (physical-under? r native))] r)))
          ready? (empty? busy)
          timeout? (and timeout? (not ready?))]
      (when (or (not= before after)
                (if timeout?
                  (not (and (= ::m/join-timeout (:error refusal)) (= busy (set (:busy refusal)))))
                  (or refusal (not= ready? (:complete? observation))
                      (not= busy (set (:busy observation))))))
        [{:action action :expected-ready? ready? :busy busy :refusal refusal :observation observation}]))))

(defn cleanup-retention-errors [before after w root completing]
  (let [under? (fn [id]
                 (loop [id id seen #{}]
                   (cond (= id root) true
                         (or (nil? id) (seen id)) false
                         :else (recur (or (:owner (m/run before w id))
                                          (get-in before [:worlds w :scopes id :parent])) (conj seen id)))))
        eligible (set (for [[r row] (:runs (m/wr before w))
                            :when (and (not= [w r] completing) (under? r) (:cps-entered? row)
                                       (#{:running :parked :stale} (:status row)))] [:cps-exit w r]))
        old-participants (set (for [[n row] (get-in before [:env :native])
                                    :when (and (= :cps-exit (:kind row)) (= w (first (:owner row)))
                                               (some #{root} (:anchor row)))] n))
        participants (set/union eligible old-participants)
        captures (into {} (for [[e row] (:entities (m/wr before w))
                                :when (and (under? (:owner row)) (#{:atom :signal :deferred :mailbox} (:kind row)))]
                            [[w (:owner row) e]
                             (cond-> (select-keys row [:kind :result])
                               (= :deferred (:kind row))
                               (assoc :allocation (:allocation row)
                                      :deferred (assoc (:deferred row) :assigned? (boolean (:completed? row))))
                               (= :mailbox (:kind row)) (assoc :allocation (:allocation row) :mailbox (:mailbox row)))]))
        shared (set (concat (keys captures)
                            (mapcat #(get-in before [:env :native % :cells]) old-participants)))]
    (concat
     (for [n eligible :when (not= :cps-exit (get-in after [:env :native n :kind]))]
       {:missing-exit-ticket n})
     (for [n participants key shared
           :let [cell (get-in after [:env :cleanup-cells key])
                 old-cell (get-in before [:env :cleanup-cells key])
                 fields (case (:kind cell) :deferred [:kind :result :allocation :deferred]
                              :mailbox [:kind :result :allocation] [:kind :result])
                 payload (select-keys (or old-cell (get captures key)) fields)]
           :when (or (not (contains? (get-in after [:env :native n :cells] #{}) key))
                     (not (contains? (:holders cell #{}) n))
                     (not= payload (select-keys cell fields)))]
       {:n n :lost-retirement-cell key :expected payload :actual cell}))))

(defn- finalization-edge-errors [before action after]
  (concat
   (when (= :finalization-wait (:t action))
     (let [{:keys [world run executing?]} (get-in before [:env :threads (:th action)])
           rr (m/run before world run) n [:cps-exit world run]
           sequence (inc (:finalization-sequence rr 0))
           actual (get-in after [:env :native n])]
       (when-not (and executing? (:cps-entered? rr) (= :running (:status rr))
                      (= run (m/current before world (:spin rr)))
                      (nil? (get-in before [:env :native n]))
                      (= [world run] (:owner actual))
                      (#{:cps-finalization :cps-exit} (:kind actual))
                      (= :running (:state actual)) (= :waiting (:phase actual))
                      (= sequence (:sequence actual))
                      (= sequence (:finalization-sequence (m/run after world run)))
                      (= (physical-ancestry before world run) (:anchor actual)))
         [{:n n :invalid-finalization-registration actual}])))
   (for [[n row] (get-in before [:env :native]) :when (= :cps-finalization (:kind row))
         :let [[w r] (:owner row) actual (get-in after [:env :native n])
               resume? (and (= :finalization-resume (:t action)) (= n (:n action)))
               delivered? (and (nil? (:operation row)) (= :cleanup-deliver (:t action)) (= n (:n action))
                               (= :waiting (:phase row)) (= (:sequence row) (:sequence action)))
               terminal? (and (= :operation-terminal (:t action)) (= n (:n action))
                              (= :open (get-in row [:operation :state]))
                              (= (:op action) (get-in row [:operation :id])))
               expected (cond-> row
                          delivered? (assoc :phase :ready :delivery (:value action))
                          terminal? (assoc :phase :ready :delivery (:value action)))
               th (:th action) thread (get-in before [:env :threads th])
               inline? (and (:executing? thread) (= [w r] [(:world thread) (:run thread)]))
               expected-frame (if inline? thread
                                  (merge thread {:world w :scope r :run r :obligation-world w :executing? true}))]
         :when (if resume?
                 (or actual (not= :ready (:phase row))
                     (not (cleanup/operation-barrier? row))
                     (not= w (if (:run thread) (:world thread) (:w action)))
                     (not= :parked (:status (m/run before w r)))
                     (not= r (m/current before w (first r)))
                     (not (or inline? (nil? (:run thread))))
                     (and (not inline?)
                          (some #(= [w r] [(:world %) (:run %)])
                                (vals (get-in before [:env :threads]))))
                     (not= :running (:status (m/run after w r)))
                     (not= (:sequence row) (:finalization-sequence (m/run after w r)))
                     (not= (assoc-in (get-in before [:env :threads]) [th] expected-frame)
                           (get-in after [:env :threads])))
                 (or (not (#{:cps-finalization :cps-exit} (:kind actual)))
                     (not= (select-keys expected [:owner :state :phase :sequence :delivery])
                           (select-keys actual [:owner :state :phase :sequence :delivery]))))]
     {:n n :lost-protected-wait {:before row :after actual :resume? resume?}})))

(defn operation-edge-errors
  "Independently conserve callback input, terminal selection and physical receipts.
  Deferred assignment may publish registration readiness but never the outer result."
  [{:keys [before action after refusal]}]
  (when (and (not refusal) (not (process-loss? action)))
    (vec
     (concat
      (for [[n ticket] (get-in before [:env :native]) :let [op (:operation ticket)] :when op
            :let [actual (get-in after [:env :native n])
                  terminal? (and (= :operation-terminal (:t action)) (= (:id op) (:op action))
                                 (= :open (:state op)) (= (:sequence ticket) (:sequence action)))
                  consume? (and (#{:finalization-resume :t38} (:t action)) (nil? actual))]
            :when (or (and (= :waiting (:phase ticket))
                           (= :ready (:phase actual)) (not terminal?))
                      (and (= :open (:state op)) (contains? actual :delivery) (not terminal?))
                      (and (pos? (:physical op))
                           (or (nil? actual) (not (set/subset? (:cells ticket #{}) (:cells actual #{})))))
                      (and consume? (or (not= :terminal (:state op)) (pos? (:physical op)))))]
        {:n n :operation-bypassed {:before ticket :after actual :action action}})
      (for [[n ticket] (get-in before [:env :native])
            :let [op (:operation ticket)] [reg row] (:registrations op)
            :let [actual (get-in after [:env :native n :operation :registrations reg])]
            :when (and (= :pending (:state row)) (= :ready (:state actual)))
            :let [[w _ e] (:cell row)
                  source (m/ent before w e)
                  cell (get-in before [:env :cleanup-cells (:cell row)])
                  resource (if (and source (= (:allocation row) (:allocation source))) source cell)
                  event (or (first (:queue (m/wr before w)))
                            (:event (first (filter #(= w (:w %)) (get-in before [:env :outside])))))
                  explicit? (= :operation-deliver (:t action))
                  mailbox? (= :mailbox (:kind resource))
                  value (if explicit? (:value action) (:value event))]
            :when (or (not= {:operation (:id op) :sequence (:sequence ticket)}
                            (get-in resource [(if mailbox? :mailbox :deferred) :protected reg]))
                      (not= value (:delivery actual))
                      (not= (dissoc row :state) (dissoc actual :state :delivery :message-id))
                      (if explicit?
                        (not= [(:id op) reg] [(:op action) (:reg action)])
                        (or (not= [e (:allocation row)] [(if mailbox? (:mailbox-post event) (:deferred-assignment event)) (:allocation event)])
                            (and (= :deferred-assign (:t action))
                                 (not= (:seq event) (:seq action))))))]
        {:reg reg :invalid-operation-readiness {:before row :after actual}})
      (when (= :operation-claim (:t action))
        (let [op (:op action) reg (:reg action)
              row (get-in before [:env :native (first op) :operation :registrations reg])
              expected (cond-> {:event :continuation-entry :op op :reg reg :continuation reg
                                :variant :ok :value (:delivery row)}
                         (:message-id row) (assoc :message-id (:message-id row)))
              entries (filter #(= :continuation-entry (:event %)) (:events after))]
          (when-not (= [expected] (vec entries))
            [{:reg reg :missing-supplied-continuation {:expected expected :actual (vec entries)}}])))
      (when (and (= :operation-terminal (:t action))
                 (= :open (get-in before [:env :native (:n action) :operation :state]))
                 (= (:op action) (get-in before [:env :native (:n action) :operation :id]))
                 (= (:sequence action) (get-in before [:env :native (:n action) :sequence])))
        (let [expected {:event :operation-terminal :op (:op action) :variant (:variant action) :value (:value action)}]
          (when-not (some #{expected} (:events after))
            [{:op (:op action) :missing-operation-terminal expected}])))))))

(defn cleanup-edge-errors
  "TL21: derive payload retention from BEFORE ownership, not a manifest.
  Explicit retirement requests and independently visible retirement effects
  cover nested cancellation and normalization. Conserve issued tickets until
  their own physical return."
  [{:keys [before action after refusal observation]}]
  (when (and (get-in before [:model :cps-exit?]) (not refusal) (not observation)
             (not (process-loss? action)))
    (let [w (:w action)
          effective (loop [a action]
                      (case (:t a)
                        :t21 (if-let [body (:body a)] (recur body) a)
                        :queued (if-let [body (:action (first (:queue (m/wr before (:w a)))))] (recur body) a)
                        a))
          completing (when (and (= :t07 (:t effective))
                                (= :running (:status (m/run before (:w effective) (:r effective))))
                                (= (:r effective) (m/current before (:w effective) (first (:r effective)))))
                       [(:w effective) (:r effective)])
          requested (case (:t action)
                      (:t10 :t11) [[w (:r action)]]
                      :t13 [[w (:scope action)]]
                      :t34 [[w (:root (m/wr before w))]]
                      :t15 (for [[r rr] (:runs (m/wr before w))
                                 :when (#{:running :parked} (:status rr))] [w r])
                      [])
          retired (concat
                   (for [ev (:events after) :when (= :run-exit (:event ev))] [(:world ev) (:r ev)])
                   (for [[v r row] (runs before)
                         :when (and (:cps-entered? row) (#{:running :parked :stale} (:status row))
                                    (= :unwinding (:status (m/run after v r))))] [v r]))]
      (vec (concat
            (operation-edge-errors {:before before :action effective :after after})
            (finalization-edge-errors before effective after)
            (when (= :cleanup-adopt (:t effective))
              (let [n (:n effective) th (:th effective)
                    ticket (get-in before [:env :native n])
                    frame (get-in before [:env :threads th])
                    expected-frame (assoc frame :cleanup-ticket n :retired? true :anchor (:anchor ticket))]
                (when-not (and (= :cps-exit (:kind ticket)) (= :ready (:phase ticket))
                               (:executing? frame) (nil? (:cleanup-ticket frame))
                               (= (:owner ticket) [(:world frame) (:run frame)])
                               (= (assoc-in (get-in before [:env :threads]) [th] expected-frame)
                                  (get-in after [:env :threads]))
                               (= (assoc (dissoc ticket :operation) :phase :claimed) (get-in after [:env :native n])))
                  [{:n n :invalid-cleanup-adoption {:thread th :before frame
                                                    :after (get-in after [:env :threads th])}}])))
            (mapcat (fn [[v root]] (cleanup-retention-errors before after v root completing))
                    (set (concat requested retired)))
            (for [[n row] (get-in before [:env :native]) :when (= :cps-exit (:kind row))
                  :let [return? (and (= :t38 (:t action)) (= :returning (:phase row))
                                     (= n (get-in before [:env :threads (:th action) :cleanup-ticket])))
                        current (get-in after [:env :native n])]
                  :when (if return? current
                            (or (not= (:owner row) (:owner current))
                                (not (set/subset? (:cells row #{}) (:cells current #{})))))]
              {:n n :ticket-conservation {:before row :after current :physical-return? return?}}))))))

(declare normalization-errors)

(defn ordinary-edge-check
  "Finite safety obligations for one transaction; events are independently checked
  against before/after rows as well as audited causes. No violation allowlist here."
  [{:keys [before action after refusal] :as edge}]
  (let [t (:t action) w (m/acting-world before action) events (if (or refusal (= :join t)) [] (:events after))
        before-obs (set (for [[v o ob] (obligations before) :when (not (:standing? ob))] [v o]))
        after-obs (set (map #(subvec (vec %) 0 2) (obligations after)))
        exits (filter #(= :obligation-exit (:event %)) events)
        removed (set/difference before-obs after-obs)
        exit-ids (set (map #(vector (:world %) (:o %)) exits))
        body-entries (filter #(= :body-entry (:event %)) events)]
    (vec
     (keep identity
           [(when-let [bad (seq (release-edge-errors edge))] {:id :TL24 :evidence (vec bad)})
            (when-let [bad (seq (timer-edge-errors edge))] {:id :TL23 :evidence (vec bad)})
            (when-let [bad (seq (mailbox-edge-errors edge))] {:id :TL22 :evidence (vec bad)})
            (when-let [bad (seq (cleanup-edge-errors edge))] {:id :TL21 :evidence (vec bad)})
            (when-let [bad (seq (join-errors edge))] {:id :TL19 :evidence (vec bad)})
            (when-let [bad (seq (released-join-evidence-errors edge))] {:id :TL19 :evidence (vec bad)})
            (when (and (not refusal) (not= t :t31)
                       (seq (set/difference removed exit-ids)))
              {:id :TL2 :evidence {:lost (set/difference removed exit-ids)}})
            (when (some #(and (not (get-in % [:ob :standing?]))
                              (not (#{:delivered :cancel-delivered :creditor-cancelled} (:cause %)))) exits)
              {:id :TL2 :evidence {:exits exits}})
            (when (some #(and (:completed? %) (or (seq (:reasons %)) (:reachable? %))
                              (not (#{:track :reactive :dirty :rerun!} (:cause %)))) body-entries)
              {:id :TL3 :evidence {:entries body-entries}})
            (when (and (#{:t16 :t17} t) (not refusal)
                       (not= (m/non-idle-projection before) (m/non-idle-projection after)))
              {:id :TL4 :evidence {:action action}})
            (when (and (= :t07 t) (or (nil? (m/run before w (:r action)))
                                      (= :unwinding (:status (m/run before w (:r action)))))
                       (not= (dissoc before :events) (dissoc after :events)))
              {:id :TL5 :evidence {:action action}})
            (let [th (get-in before [:env :threads (:th action)])
                  r (:run th) v (:world th)]
              (when (and (= :unwinding (:status (m/run before v r)))
                         (or (some #(and (= v (first %)) (= r (:owner (nth % 2)))) (entities after))
                             (some #(and (= v (first %)) (= r (:owner (nth % 2)))
                                         (not= :unwinding (:status (nth % 2)))) (runs after))
                             (some #(= [:run v r] (:creditor (nth % 2))) (obligations after))
                             (and (#{:t01 :t02 :t03 :t04 :t05 :t12 :t19 :t20 :t20q :deferred-create :deferred-observe} t)
                                  (not (and refusal (= before after)
                                            (= (if (= :released (:status (m/wr before v)))
                                                 ::m/released ::m/cancelled) (:error refusal)))))))
                {:id :TL5 :evidence {:unwinding-slice r :action action}}))
            (when (and (= :t06 t) (nil? (get-in before [:worlds w :obligations (:o action)]))
                       (not= (m/non-idle-projection before) (m/non-idle-projection after)))
              {:id :TL5 :evidence {:action action}})
            (when (and (= :t20q t) (not refusal))
              (let [c (:c action)
                    p1 (-> before (m/step (assoc action :t :t20)) (m/step {:t :t21 :c c}))
                    projected (update-in after [:cuts c] dissoc :protocol)]
                (when (or (not= p1 projected) (seq (:events after)))
                  {:id :TL13 :evidence {:quiescent-cut-not-zero-drain c}})))
            (when (and (cut-transitions t) (not refusal))
              (when-let [bad (seq (cut-footprint-errors before action after))]
                {:id :TL6 :evidence (vec bad)}))
            (when (and w (not refusal) (not (or (cut-transitions t) (#{:t19 :t31} t))))
              (let [illegal
                    (for [[v old] (:worlds before) :when (not= v w)
                          field (writes old (m/wr after v))
                          :when (not (#{:fdeps :releasing :queue} field))
                          :when (not (and (= :entities field)
                                          (= (dissoc (:entities old) [:fork w])
                                             (dissoc (:entities (m/wr after v)) [:fork w]))))]
                      {:world v :field field})]
                (when (seq illegal) {:id :TL6 :evidence (vec illegal)})))
            (when (and (#{:t10 :t11 :t13 :t34 :t36} t) (seq (l03 after)))
              {:id :TL7 :evidence (l03 after)})
            (when (and (not refusal) (not= :t31 t))
              (when-let [bad (seq (owner-release-errors before after))]
                {:id :TL7 :evidence (vec bad)}))
            (when (or (some #(#{:sealed :released} (:status (m/wr before (:world %)))) body-entries)
                      (some #(and (= :resume (:event %))
                                  (#{:sealed :released} (:status (m/wr before (:world %))))) events))
              {:id :TL8 :evidence {:entries body-entries :events events}})
            (when (and (= :t26 t) (= :merge (:kind action)) (not (:force action))
                       (not (m/quiescent? before (:world (m/cap before (:k action)))))
                       (not (and refusal (= before after) (= ::m/not-quiescent (:error refusal)))))
              {:id :TL9 :evidence {:action action :refusal refusal}})
            (let [new-terminal
                  (for [[k cap] (m/all-caps after)
                        :when (and (#{:merged :discarded} (:disposition cap))
                                   (not= (:disposition cap) (:disposition (m/cap before k))))] k)]
              (when (and (seq new-terminal) (not= :t29 t))
                {:id :TL10 :evidence {:caps (vec new-terminal) :action action}}))
            (when (some #(and (= :adapter-effect (:event %)) (:duplicate? %) (:logical-execution? %)) events)
              {:id :TL11 :evidence {:events events}})
            (when (and (= :t30 t)
                       (let [rec (m/record before (:op action))]
                         (and rec (or (not= (:k action) (:cap rec))
                                      (not= (:payload action) (:payload-hash rec)))))
                       (not (and refusal (= before after))))
              {:id :TL11 :evidence {:action action :refusal refusal}})
            (when (and (= :t22 t) (not refusal))
              (let [bad (for [world (get-in before [:cuts (:c action) :participants :worlds])
                              :let [base (get-in after [:cuts (:c action) :basis world])
                                    held (vec (filter #(= world (:w %)) (get-in before [:env :outside])))
                                    evidence (captured-evidence before world)]
                              :when (or (not= (m/wr before world) (dissoc base :held :copy-evidence))
                                        (not= held (:held base)) (not= evidence (:copy-evidence base)))]
                          {:world world :basis-not-single-view true})]
                (when (seq bad) {:id :TL13 :evidence (vec bad)})))
            (when (and (= :t23 t) (seq (l22 after))) {:id :TL13 :evidence (l22 after)})
            (when (some #(and (= :exclusive (:event %))
                              (or (seq (:read-permits %))
                                  (not= (:components %) (vec (sort (:components %)))))) events)
              {:id :TL14 :evidence {:events events}})
            (when (or (some #(and (= :resume (:event %)) (not= (:world %) (:thread-world %))) events)
                      (and (true? (:process-live? before)) (= :t35 t) (nil? (get-in before [:env :threads (get action :th :foreign) :world]))
                           (not (and refusal (= ::m/no-world (:error refusal)) (= before after)))))
              {:id :TL15 :evidence {:action action :events events}})
            (when (seq (l13 after)) {:id :TL16 :evidence (l13 after)})
            (let [removed-work (for [[v r rr] (runs before)
                                     :when (and (m/work? rr) (nil? (m/run after v r)))] [v r])
                  accounted (set (for [ev events :when (and (= :run-exit (:event ev))
                                                            (#{:cancelled :superseded} (:cause ev)))]
                                   [(:world ev) (:r ev)]))
                  illegal (set/difference (set removed-work) accounted)]
              (when (and (not= t :t31) (seq illegal)) {:id :TL17 :evidence {:removed-work illegal :action action}}))
            (when (and (#{:t04 :t05} t) (:tok action)
                       (= :live (:status (m/wr before w)))
                       (contains? (get-in before [:env :handles (:tok action) :dropped] #{}) w)
                       (not (and refusal (= ::m/idle-cache-released (:error refusal)) (= before after))))
              {:id :TL18 :evidence {:action action :refusal refusal}})
            (when-let [bad (seq (normalization-errors edge))]
              {:id :TL20 :evidence (vec bad)})]))))

(defn normalization-errors
  "TL20: ordinary local publication leaves no unrooted completed execution.
   Derive this from reachability and rows, independently of Rule L. GC only
   changes storage; foreign worlds wait for their own publication."
  [{:keys [before action after refusal observation]}]
  (when (and (not refusal) (not observation)
             (not (#{:t16 :t17 :join} (:t action))))
    (when-let [w (m/acting-world before action)]
      (when (and (m/wr after w) (not= :released (:status (m/wr after w))))
        (let [live (m/rooted-liveness after)]
          (vec (for [[r rr] (:runs (m/wr after w))
                     :when (and (= :completed (:status rr))
                                (not (contains? live [:run w r])))]
                 {:w w :r r :spin (:spin rr) :status (:status rr)})))))))

(defn execution-edge-check [{:keys [before action after refusal] :as edge}]
  (binding [m/*liveness-cache* (or m/*liveness-cache* (volatile! nil))]
    (let [aborted (for [[c cut] (:cuts before)
                        :when (and (not= :t25 (:t action)) (m/active-cuts (:phase cut))
                                   (= :failed (get-in after [:cuts c :phase])))] c)]
      (cond
        refusal (ordinary-edge-check edge)
        (seq aborted)
        (let [parts (reductions (fn [s c] (m/t25-cut-fail s {:c c})) before aborted)]
          (vec (concat
                (mapcat (fn [[a b c]]
                          (concat (check b) (ordinary-edge-check {:before a :action {:t :t25 :c c} :after b})))
                        (map vector parts (rest parts) aborted))
                (execution-edge-check (assoc edge :before (last parts))))))
        (= :t21 (:t action))
        (let [w (first (get-in before [:cuts (:c action) :participants :worlds]))
              sub (or (:body action) (when (seq (:queue (m/wr before w))) {:t :queued :w w}))
              intermediate (if sub (m/step before sub) before)]
          (vec (concat (when sub (concat (check intermediate)
                                         (execution-edge-check {:before before :action sub :after intermediate})))
                       (ordinary-edge-check (assoc edge :before intermediate)))))
        :else (ordinary-edge-check edge)))))

;; Independent retirement proof. Intentionally does not call model owner-chain, step,
;; retirement helpers, or inspect the newly stamped anchor to derive expected.
(defn retirement-before-chain [state world run]
  (loop [id run seen #{} chain []]
    (let [row (get-in state [:worlds world :runs id])]
      (cond
        (nil? id) (conj chain world)
        (contains? seen id) chain
        (= :unwinding (:status row)) (into chain (:anchor row))
        :else (recur (or (:owner row) (get-in state [:worlds world :scopes id :parent]))
                     (conj seen id) (conj chain id))))))

(defn retirement-anchor-errors [{:keys [before action after refusal]}]
  ;; These entrypoints only tear down. Compound rerun/adoption actions need a
  ;; separate independent intermediate-forest oracle before extending this set.
  (when (and (not refusal) (#{:t10 :t11 :t13} (:t action)))
    (vec
     (concat
      (for [[w world] (:worlds before)
            [r prior] (:runs world)
            :let [current (get-in after [:worlds w :runs r])]
            :when (and (not= :unwinding (:status prior)) (= :unwinding (:status current)))
            :let [expected (retirement-before-chain before w r)]
            :when (not= expected (:anchor current))]
        {:kind :ordinary-retirement-anchor :world w :run r
         :expected expected :actual (:anchor current)})
      (for [[n current] (get-in after [:env :native])
            :let [[w r] (:owner current)
                  prior-run (get-in before [:worlds w :runs r])
                  prior (get-in before [:env :native n])]
            :when (and prior-run (= :cps-exit (:kind current)) (:retired? current)
                       (not (:retired? prior)))
            :let [expected (retirement-before-chain before w r)]
            :when (not= expected (:anchor current))]
        {:kind :cleanup-retirement-anchor :ticket n :world w :run r
         :expected expected :actual (:anchor current)})))))

(defn fork-entry-errors [{:keys [before action after refusal]}]
  ;; A copied continuation is not execution in the new world's incarnation.
  ;; Inspect the newly attached rows directly, independently of copy helpers.
  (let [v (:v action)]
    (when (and (not refusal) (#{:t19 :t23} (:t action))
               (not (contains? (:worlds before) v)))
      (vec (for [[r row] (get-in after [:worlds v :runs])
                 :when (true? (:cps-entered? row))]
             {:world v :run r :copied-run-already-entered true})))))

(defn cleanup-proof-graph [{:keys [before action after]}]
  (let [delivery (custody-effective-delivery before action)
        forest (custody-reentry-forest before action after)]
    (reduce
     (fn [graph [k cap]]
       (let [source (:holder cap)
             path (when-not (m/terminal (:disposition cap)) (custody-reentry-path before action after cap forest))
             retired? (or (:closed? path)
                          (and (= source (:holder path source)) (custody-owner-retired? before after source)))
             origin (or (:origin path) source)
             next (m/cap after k) [tag id] (:holder next)
             sealing? (and (= :t26 (:t delivery)) (= k (:k delivery)))
             operation (if sealing? (:op delivery) (:op cap))]
         (if (and (not (m/terminal (:disposition cap))) (= :execution-owner (first source))
                  retired? (= :cleanup tag))
           (assoc-in graph [(second origin) id]
                     {:target-world (:world cap) :cap k :op (or operation [:custody-op id])}) graph)))
     (or (get-in before [:env :cleanup-targets]) {}) (m/all-caps before))))

(defn cleanup-target-errors [s]
  (let [graph (get-in s [:env :cleanup-targets])]
    (vec
     (concat
      (when (and (contains? (:env s) :cleanup-targets) (empty? graph)) [{:empty-cleanup-target-table true}])
      (for [[w rows] graph :when (or (empty? rows) (not (contains? (:worlds s) w)))]
        {:invalid-cleanup-source w})
      (for [[w rows] graph [id debt] rows
            :let [cap (m/cap s (:cap debt)) claim (get-in s [:custody :claims id])]
            :when (or (not= #{:target-world :cap :op} (set (keys debt)))
                      (not= (:target-world debt) (:world cap)) (nil? (:op debt))
                      (not= [:cleanup id] (:holder cap))
                      (if claim
                        (or (not= w (second (:origin claim)))
                            (not= (:cap debt) (:cap claim)) (not= (:op debt) (:settlement-op claim)))
                        (not (cleanup-terminal-proof? s debt))))]
        {:invalid-cleanup-target {:source w :claim id :debt debt}})))))

(defn cleanup-target-edge-errors [{:keys [before action after refusal] :as edge}]
  (when (and (not refusal) (not= :t31 (:t action)))
    (let [graph (cleanup-proof-graph edge)
          ready (composed-ready-proof after graph)
          expected (into {} (keep (fn [[w rows]]
                                    (let [rows (into {} (remove (fn [[_ debt]]
                                                                  (and (contains? ready (:target-world debt))
                                                                       (cleanup-terminal-proof? after debt))) rows))]
                                      (when (seq rows) [w rows]))) graph))]
      (vec
       (concat
        (when (not= expected (get-in after [:env :cleanup-targets] {}))
          [{:cleanup-target-conservation {:expected expected :actual (get-in after [:env :cleanup-targets])}}])
        (for [[w row] (get-in after [:env :releases])
              :when (not= (= :joined (:phase row)) (contains? ready w))]
          {:premature-or-missing-composed-join w})
        (cleanup-target-errors after))))))

(defn edge-check [{:keys [after refusal action] :as edge}]
  (vec (concat (execution-edge-check edge)
               (when-let [bad (seq (cleanup-target-edge-errors edge))]
                 [{:id :CleanupTargets :evidence bad}])
               (when-let [bad (seq (fork-entry-errors edge))]
                 [{:id :ForkEntry :evidence bad}])
               (when-let [bad (seq (retirement-anchor-errors edge))]
                 [{:id :RetirementAnchor :evidence bad}])
               (when (and (not refusal) (not= :join (:t action)))
                 (for [[owner n] (frequencies
                                  (for [event (:events after) :when (= :run-exit (:event event))]
                                    [(:world event) (:r event)]))
                       :when (> n 1)]
                   {:id :RunExitOnce :evidence {:owner owner :count n}}))
               (when-let [bad (seq (custody-edge-errors edge))]
                 [{:id :CustodyTransition :evidence (vec bad)}]))))

(defn check-trace
  "§4.6. Trace is [{:before s :action a :after s' :refusal optional} ...].
  TL12/TL13 progress needs an explicitly fair *maximal* suffix; depth truncation
  alone is never failure. Pass {:maximal? true :adapters-answer? true :crashes-stop? true
  :cut-boundaries? true} only when justified. TL4 pairwise replay is in generative-check."
  ([trace] (check-trace trace {}))
  ([trace {:keys [maximal? adapters-answer? crashes-stop? cut-boundaries?]}]
   (let [resumes (mapcat
                  (fn [edge]
                    (for [ev (:events (:after edge)) :when (and (not (:refusal edge))
                                                                (not= :join (get-in edge [:action :t]))
                                                                (or (= :resume (:event ev))
                                                                    (and (= :host-delivery (:event ev)) (:causal? ev))))
                          key (cond-> [(if (= :host-delivery (:event ev)) [:host (:world ev) (:o ev)]
                                           [(:world ev) (:r ev) (:o ev)])]
                                (:one-shot? ev) (conj [(:world ev) (:o ev)]))] key)) trace)
         duplicates (filter #(> (val %) 1) (frequencies resumes))
         last-state (:after (last trace))
         incomplete (filter #(#{:settling :incomplete} (:disposition (val %)))
                            (m/all-caps last-state))
         cuts (filter #(m/active-cuts (:phase (val %))) (:cuts last-state))]
     (vec (concat
           (mapcat edge-check trace)
           (when (seq duplicates) [{:id :TL1 :evidence (vec duplicates)}])
           (let [entries (for [edge trace :when (not (:refusal edge))
                               ev (:events (:after edge)) :when (= :continuation-entry (:event ev))]
                           [(:op ev) (:reg ev) (:continuation ev)])
                 repeated (filter #(> (val %) 1) (frequencies entries))]
             (when (seq repeated) [{:id :TL1 :evidence {:duplicate-continuation-entries (vec repeated)}}]))
           (let [entries (for [edge trace :when (not (:refusal edge))
                               ev (:events (:after edge))
                               :when (#{:mailbox-entry :mailbox-rejection-entry} (:event ev))]
                           [(:world ev) (:e ev) (:consumer ev)])
                 repeated (filter #(> (val %) 1) (frequencies entries))]
             (when (seq repeated) [{:id :TL1 :evidence {:duplicate-mailbox-entries (vec repeated)}}]))
           (let [entries (for [edge trace :when (not (:refusal edge))
                               ev (:events (:after edge)) :when (= :timer-entry (:event ev))] (:n ev))
                 repeated (filter #(> (val %) 1) (frequencies entries))]
             (when (seq repeated) [{:id :TL1 :evidence {:duplicate-timer-entries (vec repeated)}}]))
           (when (and maximal? adapters-answer? crashes-stop? (seq incomplete)
                      (not-any? #(some :permanent? (:steps %)) (vals (m/all-records last-state))))
             [{:id :TL12 :evidence {:nonterminal (into {} incomplete)}}])
           (when (and maximal? cut-boundaries? (seq cuts))
             [{:id :TL13 :evidence {:active-cuts (into {} cuts)}}]))))))
