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
          :when (and (:discard ev) (nil? (m/cap s (:discard ev))))]
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
   :queue (count (:queue world))})
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
                    (for [[index size] (census world) :when (> size (+ (* census-constant n) (* census-constant control)))]
                      {:w w :index index :size size :rows n :control control :c census-constant})
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
              :when (not (and (m/quiescent? s (:world cap)) (m/joined? s (:world cap))))]
          {:k k :world (:world cap) :disposition (:disposition cap)}))))

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
                        (and (:restarted? s) (:durable? cap) (#{:open :sealed} (:disposition cap))))]
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
                native (filter #(and (= [w r] (:owner %)) (not= :joined (:state %)))
                               (vals (get-in s [:env :native])))
                retired? (or (:retired? rr) (some :retired? threads) (some :retired? native))
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
          :when (and (:retired? nr) (not= :joined (:state nr))
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

(def predicates
  [[:L1 l01] [:L2 l02] [:L3 l03] [:L4 l04] [:L5 l05] [:L6 l06]
   [:L7 l07] [:L8 l08] [:L9 l09] [:L10 l10] [:L11 l11] [:L12 l12]
   [:L13 l13] [:L14 l14] [:L15 l15] [:L16 l16] [:L17 l17] [:L18 l18]
   [:L19 l19] [:L20 l20] [:L21 l21] [:L22 l22] [:L23 l23] [:L24 l24] [:L25 l25] [:L26 l26] [:L27 cleanup/errors]])
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
                 :when (and (= w world) (not= :joined (:state native)))
                 :let [expected (physical-ancestry before w r)]
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
          busy (if (= :released (:status (m/wr before w)))
                 (set (concat
                       (keep (fn [thread]
                               (when (and (:run thread) (= w (:world thread))
                                          (or (= x w) (= x (:run thread)) (some #{x} (:anchor thread))))
                                 (:run thread))) (vals (get-in before [:env :threads])))
                       (keep (fn [native]
                               (let [[world r] (:owner native)]
                                 (when (and (= w world) (not= :joined (:state native))
                                            (or (= x w) (= x r) (some #{x} (:anchor native)))) r)))
                             (vals (get-in before [:env :native]))))) busy)
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
                                :when (and (under? (:owner row)) (#{:atom :signal} (:kind row)))]
                            [[w (:owner row) e] (select-keys row [:kind :result])]))
        shared (set (concat (keys captures)
                            (mapcat #(get-in before [:env :native % :cells]) old-participants)))]
    (concat
     (for [n eligible :when (not= :cps-exit (get-in after [:env :native n :kind]))]
       {:missing-exit-ticket n})
     (for [n participants key shared
           :let [cell (get-in after [:env :cleanup-cells key])
                 old-cell (get-in before [:env :cleanup-cells key])
                 payload (or (some-> old-cell (select-keys [:kind :result])) (get captures key))]
           :when (or (not (contains? (get-in after [:env :native n :cells] #{}) key))
                     (not (contains? (:holders cell #{}) n))
                     (not= payload (select-keys cell [:kind :result])))]
       {:n n :lost-retirement-cell key :expected payload :actual cell}))))

(defn cleanup-edge-errors
  "TL21: derive payload retention from BEFORE ownership, not a manifest.
  Explicit retirement requests and independently visible retirement effects
  cover nested cancellation and normalization. Conserve issued tickets until
  their own physical return."
  [{:keys [before action after refusal observation]}]
  (when (and (get-in before [:model :cps-exit?]) (not refusal) (not observation)
             (not= :t31 (:t action)))
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
           [(when-let [bad (seq (cleanup-edge-errors edge))] {:id :TL21 :evidence (vec bad)})
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
                             (and (#{:t01 :t02 :t03 :t04 :t05 :t12 :t19 :t20 :t20q} t)
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
                      (and (= :t35 t) (nil? (get-in before [:env :threads (get action :th :foreign) :world]))
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

(defn edge-check [{:keys [before action after refusal] :as edge}]
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
                (edge-check (assoc edge :before (last parts))))))
        (= :t21 (:t action))
        (let [w (first (get-in before [:cuts (:c action) :participants :worlds]))
              sub (or (:body action) (when (seq (:queue (m/wr before w))) {:t :queued :w w}))
              intermediate (if sub (m/step before sub) before)]
          (vec (concat (when sub (concat (check intermediate)
                                         (edge-check {:before before :action sub :after intermediate})))
                       (ordinary-edge-check (assoc edge :before intermediate)))))
        :else (ordinary-edge-check edge)))))

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
           (when (and maximal? adapters-answer? crashes-stop? (seq incomplete)
                      (not-any? #(some :permanent? (:steps %)) (vals (m/all-records last-state))))
             [{:id :TL12 :evidence {:nonterminal (into {} incomplete)}}])
           (when (and maximal? cut-boundaries? (seq cuts))
             [{:id :TL13 :evidence {:active-cuts (into {} cuts)}}]))))))
