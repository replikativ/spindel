(ns spindel.v2.oracle
  "Differential oracle: replays an engine commit log (spec §11.4) through the compiled model step
  (`spindel.v2.engine/world-step`) and compares, per commit, the accepted flag, the projection
  (EDN space, id-keyed, only fields the model holds) and the model's honest flags and invariant
  tripwire.

  Log format (oracle contract, notes/PLAN.md): a vector of
  `{:item [:tag ...] :accepted bool :proj {table {id row-map}}}`; nil = none (model 0), enums as
  keywords, values/continuations opaque Nats (interned by the engine's verify ns).

  Parts:
    codes        keyword <-> model Nat codes (state.clj encodings)
    world->proj  model World -> engine projection shape
    proj->world  engine projection -> model World (re-sync; lossy fields listed in its docstring)
    canon/diff   comparison normal form (agreed deviations) and a precise diff
                 [{:table :id :field :engine :model}]
    adapt        engine item -> model Item: the step.clj table order is accepted as is (by
                 constructor name and arity, read from the kernel's `Item` inductive, so new
                 constructors are covered automatically); engine-shaped payloads go through
                 `engine-adapters` (one function per tag, delete an entry when the engine emits
                 the table order); `:start`/`:resume` are scheduling markers; anything else is
                 skipped and the driver re-syncs from the engine projection
    replay       the driver; `summary` the report map"
  (:require [clojure.edn :as edn]
            [clojure.set :as set]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.edits :as ed]
            [spindel.v2.retain :as rt]
            [spindel.v2.step :as st]
            [spindel.v2.inv :as inv]
            [spindel.v2.rule :as r]
            [spindel.v2.engine :as en]
            [spindel.v2.casc :as casc]
            [spindel.v2.acts :as acts]))

;; ===========================================================================
;; Codes (state.clj)

(def scope-kinds [:root :run :explicit])
(def run-acts [:active :parked :done])
(def run-modes [:normal :unwinding])
(def edge-kinds {0 :wait 1 :dep 2 :observe 3 :savepoint})
(def edge-phases [:armed :fired])
(def act-modes [:one :all :any])
(def res-phases [:armed :fired :cancelling])
(def source-kinds [:signal :cell :deferred :mailbox :semaphore :rerun])
(def res-kinds [:timer :external :offload :native])

(defn- index-of [v x] (let [i (.indexOf ^java.util.List v x)] (when (neg? i) (throw (ex-info "unknown code" {:v v :x x}))) i))
(defn- code-of
  "Nat code of an enum value; Nats pass through (the engine may already emit codes)."
  [v x] (if (keyword? x) (index-of v x) x))
(defn- kw-of [v x] (if (keyword? x) x (nth v x)))

(def item-codes
  "Keyword payloads of items: the enum sets are disjoint, so one map suffices."
  (merge (zipmap source-kinds (range)) (zipmap res-kinds (range)) (zipmap act-modes (range))
         ;; a savepoint is an offload-kind resource in the model (sys.clj `rk-savepoint`)
         {:none 0 :ok 1 :err 2 :savepoint (.indexOf ^java.util.List res-kinds :offload)}))

(defn- opt0 [x] (when-not (or (nil? x) (zero? x)) x))
(defn- nil0 [x] (or x 0))

(defn- result->edn [res]
  (case (long (:tag res)) 0 nil 1 [:ok (:val res)] 2 [:err (:val res)]))
(defn- edn->result [x]
  (if (nil? x) (s/->RunResult 0 0) (s/->RunResult (case (first x) :ok 1 :err 2) (second x))))

;; ===========================================================================
;; Model World -> engine projection shape

(defn world->proj
  "The model World in the engine's projection shape (verify.clj `projection`)."
  [w]
  (let [tbl (fn [rows f] (into (sorted-map) (map (fn [x] [(:id x) (f x)])) rows))]
    {:scopes (tbl (:scopes w) (fn [x] {:parent (opt0 (:parent x)) :kind (kw-of scope-kinds (:kind x)) :open (:open x)}))
     :comps (tbl (:comps w)
                 (fn [c] {:owner (opt0 (:owner c)) :inputs (let [x (:inputs c)] (if (sequential? x) (vec x) x)) :body (:body c) :run (opt0 (:run c))
                          :epoch (:epoch c) :done-epoch (opt0 (:done-epoch c)) :pending (:pending c)
                          :rank (:rank c) :version (:version c) :result (result->edn (:result c))
                          :idle (:idle c)
                          :validity (let [vs (:validity c)]
                                      (cond (some #(zero? (:debtor %)) vs) :invalid
                                            (seq vs) (mapv (juxt :debtor :version) vs)))
                          :basis (mapv (juxt :id :at) (:basis c))
                          :adoption (when (or (seq (:adopt-basis c)) (seq (:adopt-baselines c)))
                                      {:basis (mapv :id (:adopt-basis c))
                                       :baselines (mapv (juxt :site :source :value) (:adopt-baselines c))})
                          :handles (:handles c)}))
     :tasks (tbl (:tasks w) (fn [k] (cond-> {:owner (opt0 (:owner k)) :run (opt0 (:run k))
                                             :result (result->edn (:result k)) :handles (:handles k)}
                                      (contains? k :inputs) (assoc :inputs (vec (:inputs k))))))
     :runs (tbl (:runs w)
                (fn [x] {:of (:of x) :stamp (:stamp x) :epoch (:epoch x) :scope (:scope x)
                         :act (kw-of run-acts (:act x)) :mode (kw-of run-modes (:mode x)) :slice (:slice x)
                         :effect-index (:effect-index x) :finalizers (vec (repeat (count (:finalizers x)) 0))
                         :resources (vec (:resources x))}))
     :sources (tbl (:sources w)
                   (fn [x] {:owner (opt0 (:owner x)) :kind (kw-of source-kinds (:kind x)) :state (:state x)
                            :version (:version x) :open (:open x) :handles (:handles x)}))
     :edges (tbl (:edges w)
                 (fn [e] (let [k (edge-kinds (:kind e))]
                           {:kind k :creditor (:creditor e) :debtor (:debtor e)
                            ;; observe: the engine holds the callback as the creditor and projects
                            ;; cont = restart; the model keeps cb in cont (not compared)
                            :cont (if (or (zero? (:cont e)) (= k :observe)) :restart (:cont e)) :at (:at e)
                            :phase (kw-of edge-phases (:phase e)) :marked (:marked e)
                            :seen (when (:has-seen e) (:seen e))
                            ;; the engine projects (value, seen) for dep edges on sources
                            :baseline (when (and (= k :dep) (s/source-has w (:debtor e)))
                                        [(:base-value e) (when (:has-seen e) (:seen e))])})))
     :acts (tbl (:acts w)
                (fn [x] {:run (:run x) :mode (kw-of act-modes (:mode x))
                         :members (vec (sort-by second (map (juxt :edge :idx) (:members x))))
                         :slots (mapv result->edn (:slots x)) :remaining (:remaining x) :cont (:cont x)}))
     :res (tbl (:res w) (fn [z] {:owner (:owner z) :kind (kw-of res-kinds (:kind z)) :at (:at z)
                                 :phase (kw-of res-phases (:phase z))}))
     :cleanup (into (sorted-map) (map (fn [c] [(:run c) {:rows (vec (:rows c))}])) (:cleanup w))
     :pubs (tbl (:pubs w) (fn [p] {:edge (:edge p) :basis (vec (:basis p)) :handles (:handles p)}))
     :forks (tbl (:forks w) (fn [f] {:child (:child f) :owner (:owner f)}))
     :pins (into (sorted-map) (frequencies (:pins w)))
     :pending-act (opt0 (:pending-act w))
     :released (:released w)
     :next-id (:next-id w)}))

;; ===========================================================================
;; Engine projection -> model World (re-sync)

(defn- newest-first [m] (sort-by (comp - key) m))

(defn- with-new-fields
  "A row from its record constructor, adding the `extra` fields the model's row has (fields
  being added by the parallel model pass: task inputs, source queue), so the oracle works
  before and after."
  [ctor m extra]
  (let [ks (set (keys (ctor {})))]
    (ctor (merge m (select-keys extra (filter ks (keys extra)))))))

(defn- inputs-val
  "Engine inputs: an interned Nat (samples 1-3) or a vector of interned Nats (engine after
  d43a321). The model's inputs are (List Nat): a single Nat n is [n], nil is []."
  [x] (cond (sequential? x) (vec x) (nil? x) [] :else [x]))

(defn opaque-finalizers [n] (vec (repeat n (s/map->Finalizer {:f 0 :at 0 :refs []}))))

(defn proj->world
  "The model World of an engine projection. Lossy where the projection is (reconstructed):
  - edge `base-version` := the projected seen (the engine projects (value, seen));
  - adoption basis `at` := 0 and adoption baseline `version` := 0 (not projected);
  - run finalizers := N opaque entries (F 0, at 0, refs []) (the engine projects a count);
  - activation `spawned` := the member debtors that are tasks owned by the run's scope (the
    engine's loser rule), since the item's `mine` list is not projected;
  - cleanup rows := `rule/cleanup-rows-of` for each projected cleanup key (the engine keeps the
    storage implicitly);
  - edge `cont` of observe edges = restart (the callback is not projected; cb 0 in the adapter).
  Rows are listed newest (largest id) first, the order `tbl-ins` produces."
  [p]
  (let [rows (fn [t f] (map (fn [[id x]] (f id x)) (newest-first (get p t))))
        w (s/map->World
           {:scopes (rows :scopes (fn [id x] (s/map->ScopeRow {:id id :parent (nil0 (:parent x)) :kind (code-of scope-kinds (:kind x)) :open (boolean (:open x))})))
            :comps (rows :comps
                         (fn [id c]
                           (let [v (:validity c)]
                             (s/map->CompRow
                              {:id id :owner (nil0 (:owner c)) :inputs (inputs-val (:inputs c)) :body (nil0 (:body c))
                               :run (nil0 (:run c)) :epoch (:epoch c) :done-epoch (nil0 (:done-epoch c))
                               :pending (:pending c) :rank (nil0 (:rank c)) :version (:version c)
                               :result (edn->result (:result c)) :idle (boolean (:idle c))
                               :validity (cond (= v :invalid) [(s/->Valid 0 0 0 0)]
                                               (sequential? v) (mapv (fn [[d ver]] (s/->Valid d ver 0 0)) v)
                                               :else [])
                               :basis (mapv (fn [[x at]] (s/->Created x at)) (:basis c))
                               :adopt-basis (mapv #(s/->Created % 0) (get-in c [:adoption :basis]))
                               :adopt-baselines (mapv (fn [[at d base]] (s/->AdoptBase at d base 0))
                                                      (get-in c [:adoption :baselines]))
                               :handles (:handles c)}))))
            :tasks (rows :tasks (fn [id k] (with-new-fields s/map->TaskRow
                                                  {:id id :owner (nil0 (:owner k)) :run (nil0 (:run k))
                                                   :result (edn->result (:result k)) :handles (:handles k)}
                                                  {:inputs (vec (:inputs k))})))
            :runs (rows :runs
                        (fn [id x]
                          (s/map->RunRow {:id id :of (:of x) :stamp (:stamp x) :epoch (:epoch x) :scope (:scope x)
                                          :act (code-of run-acts (:act x)) :mode (code-of run-modes (:mode x))
                                          :slice (boolean (:slice x)) :effect-index (:effect-index x)
                                          :finalizers (opaque-finalizers (count (:finalizers x)))
                                          :resources (vec (:resources x))})))
            :sources (rows :sources (fn [id x] (with-new-fields s/map->SourceRow
                                                {:id id :owner (nil0 (:owner x)) :kind (code-of source-kinds (:kind x))
                                                 :state (nil0 (:state x)) :version (:version x) :open (boolean (:open x))
                                                 :handles (:handles x)}
                                                {:queue (vec (:queue x))})))
            :edges (rows :edges
                         (fn [id e]
                           (let [[bv _] (:baseline e)
                                 seen (:seen e)]
                             (s/map->EdgeRow
                              {:id id :kind (get (set/map-invert edge-kinds) (:kind e) (:kind e))
                               :creditor (nil0 (:creditor e)) :debtor (nil0 (:debtor e))
                               :cont (if (= :restart (:cont e)) 0 (nil0 (:cont e))) :at (:at e)
                               :phase (code-of edge-phases (:phase e)) :marked (boolean (:marked e))
                               :has-seen (some? seen) :seen (nil0 seen)
                               :has-base (some? (:baseline e)) :base-value (nil0 bv) :base-version (nil0 seen)}))))
            :acts (rows :acts
                        (fn [id x]
                          (s/map->ActRow
                           {:id id :run (:run x) :mode (code-of act-modes (:mode x))
                            :members (mapv (fn [[e i]] (s/->Member e i)) (:members x))
                            :slots (mapv edn->result (:slots x)) :remaining (:remaining x)
                            :cont (nil0 (:cont x)) :spawned []})))
            :res (rows :res (fn [id z] (s/map->ResRow {:id id :owner (:owner z) :kind (code-of res-kinds (:kind z)) :at (:at z) :phase (code-of res-phases (:phase z))})))
            :cleanup []
            :pubs (rows :pubs (fn [id x] (s/map->PubRow {:id id :edge (:edge x) :basis (vec (:basis x)) :handles (:handles x)})))
            :pins (vec (mapcat (fn [[x n]] (repeat n x)) (sort (:pins p))))
            :forks (rows :forks (fn [id x] (s/map->ForkRow {:id id :child (:child x) :owner (:owner x)})))
            :pending-act (nil0 (:pending-act p))
            :released (boolean (:released p))
            :next-id (:next-id p)})
        ;; activation `spawned`: member debtors that are tasks owned by the run's scope
        spawned (fn [act]
                  (let [scope (some #(when (= (:run act) (:id %)) (:scope %)) (:runs w))
                        debtor (fn [e] (some #(when (= e (:id %)) (:debtor %)) (:edges w)))]
                    (vec (distinct (for [m (:members act)
                                         :let [d (debtor (:edge m))]
                                         :when (some #(and (= d (:id %)) (= scope (:owner %))) (:tasks w))]
                                     d)))))
        w (assoc w :acts (map #(assoc % :spawned (spawned %)) (:acts w)))]
    (assoc w :cleanup (for [rid (sort > (keys (:cleanup p)))
                            :let [run (some #(when (= rid (:id %)) %) (:runs w))]]
                        (s/map->CleanupRow {:run rid :rows (if run (vec (r/cleanup-rows-of w run)) [])})))))

;; ---------------------------------------------------------------------------
;; Quiescing an engine state: the engine commits some items before steps the model folds into
;; the item (granularity, see the triage in oracle_test):
;;  - slice exit: a completing run keeps `slice` until its slice returns, then T13 retires it
;;    (the model's T12 releases the slice and retires in the same step);
;;  - resume: a filled activation (remaining 0, or an `any` with a filled slot) stays until the
;;    run's next `[:schedule r]` (the model's T9 resumes at the fill, T6/T9).
;; `quiesce` applies both with the model's own functions (st/resume, rule/retire-full, then
;; Rule R). Used to re-sync and to classify a divergence as granularity-only.

(defn- act-full? [a]
  (or (zero? (:remaining a))
      (and (= s/am-any (:mode a)) (some #(pos? (:tag %)) (:slots a)))))

(defn quiesce
  "Resumes full activations whose run is parked, then exits the slices of done runs (T13) and
  applies Rule R; the world is unchanged when there is nothing to do."
  [w]
  (let [full (filter #(and (act-full? %)
                           (some (fn [x] (and (= (:run %) (:id x)) (= s/act-parked (:act x)))) (:runs w)))
                     (:acts w))
        w1 (reduce st/resume w full)
        exits (filter #(and (= s/act-done (:act %)) (:slice %)) (:runs w1))
        w2 (reduce (fn [w x] (s/run-upd w (:id x) (fn [row] (assoc row :slice false)))) w1 exits)
        w3 (reduce (fn [w x] (r/retire-full w (:id x))) w2 exits)
        ;; Z#49 logs: the engine commits `[:slice-exit r]` before T13 retires r (the retirement
        ;; shows in the next commit): retire every retirable run still in cleanup
        idle (filter #(and (st/retirable %) (some (fn [c] (= (:run c) (:id %))) (:cleanup w3))) (:runs w3))
        w4 (reduce (fn [w x] (r/retire-full w (:id x))) w3 idle)]
    (if (or (seq full) (seq exits) (seq idle)) (r/rule-r w4) w)))

(defn resync
  "The model world to continue from after an item the model cannot replay."
  [p] (quiesce (proj->world p)))

;; ===========================================================================
;; Comparison: canonical form (agreed deviations) and the diff

(def ignored-fields
  "Fields the model holds but does not maintain against the engine (compared nowhere): none
  since the model maintains I12 ranks (engine.clj B7)."
  {})

(def pending-deviations
  "Differences the comparison tolerates until the spec or the model settles them (disabled by
  `:strict? true`); each is reported in the triage (oracle_test):
  :mailbox-state  `:sources :state` of a mailbox: the engine logs v = nil and projects its
                  queue object; the model keeps the creation value in `state` and the queue
                  in `SourceRow.queue` (not projected by the engine)
  :wait-at        `:edges :at` of non-dep edges: spec §2 gives `at` a meaning for dep edges
                  only (re-entry point); the engine leaves 0, the model stores the site index"
  {:mailbox-state true :wait-at true})

(def ^:dynamic *deviations* pending-deviations)

(defn- canon-validity [v]
  (cond (= v :invalid) :invalid (empty? v) #{} :else (set v)))
(defn- canon-adoption [x]
  (let [b (set (:basis x)) bl (set (:baselines x))] (when (or (seq b) (seq bl)) {:basis b :baselines bl})))

(defn canon
  "Comparison normal form of a projection (either side). Agreed deviations: `:runs :finalizers`
  count only; `:cleanup` keys only; basis/validity/adoption/resources compare as sets; pins with a
  zero count dropped; `ignored-fields` removed; enums as keywords."
  [p]
  (letfn [(rows [t f] (into (sorted-map) (map (fn [[id x]] [id (apply dissoc (f x) (ignored-fields t))])) (get p t)))]
    {:scopes (rows :scopes #(update % :kind (partial kw-of scope-kinds)))
     :comps (rows :comps #(-> % (update :basis set) (update :validity canon-validity)
                              (update :adoption canon-adoption) (update :inputs inputs-val)))
     :tasks (rows :tasks #(cond-> % (contains? % :inputs) (update :inputs inputs-val)))
     :runs (rows :runs #(-> % (update :finalizers count) (update :resources set)
                            (update :act (partial kw-of run-acts)) (update :mode (partial kw-of run-modes))))
     :sources (rows :sources #(cond-> (update % :kind (partial kw-of source-kinds))
                                (and (:mailbox-state *deviations*) (= :mailbox (kw-of source-kinds (:kind %))))
                                (dissoc :state)))
     :edges (rows :edges #(cond-> % (and (:wait-at *deviations*) (not= :dep (:kind %))) (dissoc :at)))
     :acts (rows :acts #(-> % (update :mode (partial kw-of act-modes)) (update :members (comp vec (partial sort-by second)))))
     :res (rows :res #(-> % (update :kind (fn [k] (let [k (kw-of res-kinds k)] (get {:savepoint :offload} k k)))) (update :phase (partial kw-of res-phases))))
     :cleanup (into (sorted-set) (keys (:cleanup p)))
     :pubs (rows :pubs identity)
     :forks (rows :forks identity)
     :pins (into (sorted-map) (remove (comp zero? val)) (:pins p))
     :pending-act (:pending-act p)
     :released (boolean (:released p))
     :next-id (:next-id p)}))

(def row-tables [:scopes :comps :tasks :runs :sources :edges :acts :res :pubs :forks])

(defn diff
  "Precise differences between two projections (engine first): a vector of
  {:table :id :field :engine :model}; a missing row has :field :row and the row (or nil)."
  [ep mp]
  (let [e (canon ep) m (canon mp)]
    (vec
     (concat
      (for [t row-tables
            :let [et (get e t) mt (get m t)]
            id (sort (set/union (set (keys et)) (set (keys mt))))
            :let [er (get et id) mr (get mt id)]
            d (cond (nil? er) [{:table t :id id :field :row :engine nil :model mr}]
                    (nil? mr) [{:table t :id id :field :row :engine er :model nil}]
                    ;; only fields both sides project (the model's fields the engine projects)
                    :else (for [f (sort (set/intersection (set (keys er)) (set (keys mr))))
                                :when (not= (get er f) (get mr f))]
                            {:table t :id id :field f :engine (get er f) :model (get mr f)}))]
        d)
      (for [t [:cleanup :pins :pending-act :released :next-id]
            :when (not= (get e t) (get m t))]
        {:table t :id nil :field t :engine (get e t) :model (get m t)})))))

;; ===========================================================================
;; Items: the model's constructor table, read from the kernel

(defn item-ctors
  "{:tag {:idx n :arity k}} from the kernel's `Item` inductive (constructor order = runtime tag)."
  []
  (let [env ^ansatz.kernel.Env @a/ansatz-env
        ci (.lookup env (ansatz.kernel.Name/fromString "Item"))]
    (into {} (map-indexed (fn [i n] (let [c (.lookup env n)]
                                      [(keyword (subs (str n) (count "Item."))) {:idx i :arity (.numFields c)}]))
                          (.ctors ci)))))

(def ctors (delay (item-ctors)))
(defn ctor-idx [tag] (:idx (get @ctors tag)))
(defn ctor-tag [idx] (some (fn [[t c]] (when (= idx (:idx c)) t)) @ctors))

(def ^:private stamp-ctors
  "Items whose first field is the acting run's stamp (body effects and completion)."
  #{:create-source :track :arm :create-comp :spawn :await :complete :take :open-scope})

(defn- item [tag & fields] (into [(ctor-idx tag)] fields))
(defn- payload
  "An item field: enum keywords to codes, lists as vectors; `[:opaque x]` (the engine logs the
  raw value of a refused host item, e.g. `[:write 7 [:opaque 5]]`) is x when it is a Nat, else
  0 (the model's values are opaque Nats, A#1; a refused item changes nothing)."
  [x]
  (cond (keyword? x) (item-codes x)
        (and (sequential? x) (= :opaque (first x))) (let [v (second x)] (if (nat-int? v) v 0))
        (sequential? x) (vec x)
        :else x))

(defn- row-of [p t id] (get-in p [t id]))

(def engine-adapters
  "Engine-shaped payloads (log samples of 2026-11-03) -> model items, per tag. `ctx` =
  {:w model world before, :post engine projection after the commit, :prev engine projection
  before}. Returns {:item model-item} or {:marker kind :run r}. Delete an entry once the engine
  emits the step.clj table order for that tag (the table order is recognised by arity first,
  see `adapt`; same-arity engine shapes with the same field meaning go through that path:
  create-source-top, complete with a value, spawn [r site k] (site = opaque body))."
  {;; [:create-comp-top c]: owner, inputs, body from the committed row
   :create-comp-top (fn [{:keys [post]} [c]]
                      (let [row (row-of post :comps c)]
                        {:item (item :create-comp-top (nil0 (:owner row)) c (inputs-val (:inputs row)) (nil0 (:body row)))}))
   ;; [:create-comp r site c]
   :create-comp (fn [{:keys [post]} [rid _site c]]
                  (let [row (row-of post :comps c)]
                    {:item (item :create-comp rid c (inputs-val (:inputs row)) (nil0 (:body row)))}))
   ;; [:spawn-top k]: the owner scope from the committed row, body opaque (0)
   :spawn-top (fn [{:keys [post]} [k]]
                {:item (item :spawn-top (or (:owner (row-of post :tasks k)) s/root-scope-id) 0 k [])})
   ;; [:observe d e]: callback not projected (0 = the restart code the engine projects)
   :observe (fn [_ [d e]] {:item (item :observe d 0 e)})
   ;; [:track r x e] (computation) / [:track r x] (task snapshot): cont from the committed edge;
   ;; a reused site edge allocates nothing
   :track (fn [{:keys [w post]} [rid x e]]
            (let [cont (get-in post [:edges e :cont])
                  k (if (or (nil? cont) (= :restart cont)) 0 cont)
                  fresh (if (and e (not (s/edge-has w e))) e (:next-id w))]
              {:item (item :track rid x k fresh)}))
   ;; [:complete r tag] without a value (sample 1): the value from the committed entity
   :complete (fn [{:keys [post]} [rid tag v]]
               (let [x (:of (row-of post :runs rid))
                     res (or (:result (row-of post :comps x)) (:result (row-of post :tasks x)))]
                 {:item (item :complete rid (item-codes tag) (or v (second res) 0))}))
   ;; [:await r ds mode a]: cont from the committed activation (0 when the fast path removed
   ;; it); `mine` = the task debtors owned by r's scope (the engine's loser rule)
   :await (fn [{:keys [w post]} [rid ds mode aid]]
            (let [scope (:scope (first (s/run-find w rid)))
                  mine (vec (distinct (filter #(= scope (:owner (first (s/task-find w %)))) ds)))]
              {:item (item :await rid (vec ds) (item-codes mode) (nil0 (get-in post [:acts aid :cont])) aid mine)}))
   ;; [:dispatch c r]: T5 for a fresh or invalid idle computation, T11 otherwise
   :dispatch (fn [{:keys [w]} [c rid]]
               (let [row (first (s/comp-find w c))]
                 {:item (if (and row (en/startable w row)) (item :start c rid) (item :dispatch-comp c rid))}))
   ;; [:start r]: a task run's first slice = the scheduling choice (applied before r's next
   ;; body effect, where the engine's slice begins)
   :start (fn [_ [rid]] {:marker :schedule :run rid})
   ;; [:resume a]: the resumed run's slice (the model resumed the activation at the fill)
   :resume (fn [{:keys [prev]} [aid]] {:marker :resume :run (get-in prev [:acts aid :run])})})

(def table-aliases
  "Engine tag -> model constructor, where the names differ (table format)."
  {:dispatch :dispatch-comp})

(defn- add-inputs
  "`[:spawn st body fresh]` / `[:spawn-top scope body fresh]` (sample 3, before the inputs field):
  the model's T4 takes the task inputs as a last field; none logged = []."
  [tag]
  (fn [_ args] {:item (conj (into [(ctor-idx tag)] (map payload args)) [])}))

(defn- inputs-list
  "`[:create-comp(-top) x c inputs body]` with inputs a single interned Nat (sample 3): the
  model's inputs are a list."
  [tag]
  (fn [_ [x c i b]] {:item (item tag (payload x) c (inputs-val i) (payload b))}))

(defn- take-item
  "`[:take r x a]` (engine): the model's take carries the activation's continuation (from the
  committed activation; 0 when the take was served at once)."
  [{:keys [post]} [rid x aid]]
  {:item (item :take rid x (nil0 (get-in post [:acts aid :cont])) aid)})

(def table-adapters
  "Table-format items the model cannot take verbatim (delete when the engine catches up)."
  {:spawn (add-inputs :spawn) :spawn-top (add-inputs :spawn-top)
   :create-comp (inputs-list :create-comp) :create-comp-top (inputs-list :create-comp-top)
   :take take-item
   ;; a refused fire is logged as `[:resource-fire z]` (engine `refuse!`, sample 9 commit 21: the
   ;; resource is cancelling): the model's T18 refuses it whatever the payload (ok, 0)
   :resource-fire (fn [_ [z]] {:item (item :resource-fire z 1 0)})})

;; the legacy logs carry the same `[:take r x a]` shape; legacy `[:spawn r site k]` has no inputs
(alter-var-root #'engine-adapters assoc :take take-item :spawn (add-inputs :spawn))

(defn log-format
  "`:table` (engine >= ca72c3b: step.clj payload order, `[:schedule r]` items) or `:legacy`
  (the samples of 2026-11-03 21:59/22:24: engine-shaped payloads, `:start r`/`:resume a`)."
  [log]
  (if (some #(#{:resume} (first (:item %))) log) :legacy
      (if (some #(= :schedule (first (:item %))) log) :table :legacy)))

(defn adapt
  "Engine item -> {:item model-item} | {:marker kind :run r} | {:skip tag}. Both formats first
  try the step.clj table (constructor name, aliased, and arity)."
  [fmt ctx [tag & args]]
  (let [mtag (if (= fmt :table) (get table-aliases tag tag) tag)
        c (get @ctors mtag)
        args (vec args)]
    (cond
      (and (#{:create-comp :create-comp-top} mtag) (= 4 (count args)) (not (sequential? (nth args 2))))
      ((inputs-list mtag) ctx args)
      (and c (= (count args) (:arity c))) {:item (into [(:idx c)] (map payload args))}
      (and (= fmt :table) (table-adapters tag)) ((table-adapters tag) ctx args)
      (and (= fmt :legacy) (engine-adapters tag)) ((engine-adapters tag) ctx args)
      ;; layer 2: `[:fork-host c]` takes the child world's id from the allocator and changes no
      ;; table of the parent (the marker is the child cell's, notes/LAYER2.md §3)
      (= tag :fork-host) {:bump (first args)}
      ;; `[:fork r c]` (the effect): the delivery carrier's id and the child's, no table change
      ;; in the parent, whose run keeps its slice
      (= tag :fork) {:bump (second args)}
      :else {:skip tag})))

;; The `(fork)` effect, child side (notes/LAYER2.md L3): the forking run's copy is parked at the
;; effect and resumed with `[:child nil]`. In layer-1 items that is a resource the run arms and
;; that fires and is acknowledged at once (T17/T6, T18, T15): the run is active, out of its slice,
;; and its next item is `[:schedule r]`. The engine reserves the three ids in T17's order and
;; counts the effect in the child's run.
(defn fork-child
  "The child's world of `[:fork r c]`, from the parent's world before the fork commit:
  {:world :accepted}."
  [w-pre r]
  (let [z (:next-id w-pre)
        st (:stamp (first (s/run-find w-pre r)))
        steps (reductions (fn [o it] (en/world-step (:world o) it)) {:world w-pre :accepted true}
                          [(item :arm st s/rk-offload 0 z) (item :resource-fire z 1 0) (item :resource-ack z)])]
    {:world (:world (last steps)) :accepted (every? :accepted steps)}))

(defn skip-to
  "`w` with its allocator raised to `n` (`spindel.v2.skip/skip-ids`: iterated `bump`, which
  keeps `p3l`). The worlds of a family draw their ids from one allocator, so a world's log shows
  `next-id` jump between its own items."
  [w n]
  (loop [w w] (if (< (:next-id w) n) (recur (s/bump w)) w)))

(defn align
  "Family logs: the allocator before `it`, from the committed projection: the largest value at
  or above the model's from which the item is accepted and ends at the projection's `next-id`
  (the item itself takes at most 8 ids). `w` when there is none."
  [w it proj]
  (or (when-let [n (:next-id proj)]
        (first (for [k (range 9)
                     :let [m (- n k)]
                     :when (>= m (:next-id w))
                     :let [w2 (skip-to w m)
                           o (en/world-step w2 it)]
                     :when (and (:accepted o) (= n (:next-id (:world o))))]
                 w2)))
      w))

(defn implicit-finally
  "Finally regions open and close inside a slice (body contract §7, B3/B8) without an item in
  the log, and the model has no transition for them yet (pending: finalizer items). Before an
  item, the finalizer list of the run that executes it (the item's stamp run, or a run holding
  the slice) is set to the count the engine projects after the commit. Returns the edited
  world, or nil when nothing changes."
  [w post model-item]
  (let [st (when (stamp-ctors (ctor-tag (first model-item))) (second model-item))
        runs (filter #(and (or (= st (:stamp %)) (:slice %))
                           (when-let [er (get-in post [:runs (:id %)])]
                             (not= (count (:finalizers er)) (count (:finalizers %)))))
                     (:runs w))]
    (when (seq runs)
      (reduce (fn [w x] (s/run-upd w (:id x) (fn [row] (assoc row :finalizers
                                                              (opaque-finalizers (count (get-in post [:runs (:id x) :finalizers])))))))
              w runs))))

(defn implicit-cleanup
  "Finally exits inside a cleanup slice (B3/B8, legacy logs without finally items): the engine's
  `[:finalize r]` commits before its cleanup slice runs, and that one slice runs every finally
  block (Z#35) and retires R, with no item. A model run that is unwinding and holds the slice
  gets `finally-exit` items until its count is the engine's (0 when the engine retired it);
  the slice's return is `implicit-exits`. Returns the model items."
  [w post]
  (vec (mapcat (fn [x]
                 (let [n (count (:finalizers x))
                       m (count (get-in post [:runs (:id x) :finalizers]))
                       k (- n m)]
                   (when (pos? k) (repeat k (item :finally-exit (:stamp x))))))
               (filter #(and (:slice %) (= s/mode-unwinding (:mode %))) (:runs w)))))

(defn implicit-exits
  "The return of a cancelled run's slice (Z#35: after its last finally block, which runs after
  the `finally-exit` committed at the block's start): the engine logs no item, its projection
  just shows the run without the slice (or retired). Before an item, every model run that is
  done, holds the slice and has no open region gets `[:slice-exit r]` when the engine's
  projection after the item shows it without the slice. Returns the model items."
  [w post]
  (vec (for [x (:runs w)
             :when (and (= s/act-done (:act x)) (:slice x) (empty? (:finalizers x))
                        (not (get-in post [:runs (:id x) :slice])))]
         (item :slice-exit (:id x)))))

(defn implicit-schedule
  "The scheduling choice the engine makes on entering a slice: before a body effect or
  completion of run `st` that does not hold the slice (active, normal), the model needs [schedule st]."
  [w model-item]
  (when (stamp-ctors (ctor-tag (first model-item)))
    (let [st (second model-item)]
      (when-let [run (first (filter #(= st (:stamp %)) (:runs w)))]
        (when (and (not (:slice run)) (= s/act-active (:act run)) (= s/mode-normal (:mode run)))
          (item :schedule (:id run)))))))

;; ===========================================================================
;; One checked model step: honest flags + invariant tripwire

(defn flags
  "Rule R's honest hypotheses (rule.clj/engine.clj) and the compiled tripwire for an accepted
  raw world `rw` and the step's result `w'`."
  [rw w']
  (let [n (r/normalize (r/rule-r-pre rw))]
    {:rule-r-safe (r/rule-r-safe rw)
     :live-converged-pre (rt/live-converged n)
     :live-converged (rt/live-converged w')
     :normalized (r/normalized n)
     :filter-safe (r/filter-safe n)
     :no-orphans (r/no-orphans w')
     :inv-sample (ed/inv-sample w')
     :acts-alive (casc/acts-alive rw)
     :ga (acts/ga w')
     :i3 (s/tbl-all (partial rt/keep-fn w') (s/all-ids w'))
     :i4 (every? #(or (= s/act-done (:act %)) (rt/in-live w' (:id %))) (:runs w'))
     :step-normalized (r/normalized w')
     :inv-all (inv/inv-all w')
     ;; the spec's literal readings of I1/I5/I7/I8/I9/I10 (hold since the alignment pass; I5's
     ;; dep part since Z#48: T7 on a closed source consumes its edge)
     :lit-all (every? true? [(inv/lit-i1-scope w') (inv/lit-i10-current w') (inv/lit-i7-basis w')
                             (inv/lit-i8-sources w') (inv/lit-i8-runs w') (inv/lit-i9-res w')
                             (inv/lit-i5-dep-final w')])}))

(defn step-checked
  "world-step plus flags: {:world :accepted :failed-flags}."
  [w it]
  (let [raw (en/raw w it)
        o (en/world-step w it)]
    {:world (:world o) :accepted (:accepted o)
     :failed-flags (when (:accepted raw)
                     (vec (keep (fn [[k v]] (when-not (true? v) k)) (flags (:world raw) (:world o)))))}))

;; ===========================================================================
;; Driver

(defn roundtrip
  "Adapter self-check: commits whose projection does not survive proj->world -> world->proj
  (a mapping bug, or information the model does not hold): [{:commit :diffs}]."
  [log]
  (vec (keep-indexed (fn [i {:keys [proj]}]
                       (when proj
                         (let [d (diff proj (world->proj (proj->world proj)))] (when (seq d) {:commit i :diffs d}))))
                     log)))

(defn read-log [path] (edn/read-string (slurp path)))

(defn- cells [ds] (set (map (juxt :table :id :field) ds)))

(defn replay
  "Replays `log` through the model. Options: :format (default `log-format`), :strict? (no
  `pending-deviations`), :from (first commit index, default 0: start at
  `empty-world`, else re-sync from the projection of commit from - 1), :resync-on-divergence?
  (default false: lockstep, re-sync only after skipped items), :max-diffs (per divergence, 8),
  :init (the model world to start from, default `empty-world`: a fork's log starts from its
  parent's world at the fork commit), :family? (the log is of a world with forks: `align` the
  allocator before every item), :worlds? (keep the model world after every commit as :worlds).
  Returns the summary map."
  [log & {:keys [format from resync-on-divergence? max-diffs strict? init family? worlds?] :or {from 0 max-diffs 8}}]
  (binding [*deviations* (if strict? {} pending-deviations)]
  (let [fmt (or format (log-format log))
        ;; logs with `[:finally-enter st]`/`[:finally-exit st]` items (sample 4 on) need no
        ;; implicit finally regions or cleanup exits
        explicit-finally? (some #(#{:finally-enter :finally-exit} (first (:item %))) log)
        ;; logs with `[:slice-exit r]` items (Z#49, sample 7 on) need no implicit exits
        explicit-exits? (some #(= :slice-exit (first (:item %))) log)]
  (loop [i from
         w (if (zero? from) (or init s/empty-world) (resync (:proj (nth log (dec from)))))
         prev (when (pos? from) (:proj (nth log (dec from))))
         acc {:format fmt :commits (- (count log) from) :checked 0 :markers 0 :skipped {} :resyncs 0
              :implicit-schedules 0 :implicit-finally 0 :divergences [] :skipped-ids 0
              :worlds (when worlds? [])}]
    (if (>= i (count log))
      (let [divs (:divergences acc)
            by-i (into {} (map (juxt :commit identity)) divs)]
        (assoc acc :divergences
               (mapv (fn [d] (assoc d :caught-up?
                                    (empty? (set/intersection (cells (:diffs-all d))
                                                              (cells (:diffs-all (by-i (inc (:commit d)))))))))
                     divs)
               :n-divergences (count divs)
               :n-real (count (filter #(= :real (:class %)) divs))
               :n-granularity (count (filter #(= :granularity (:class %)) divs))))
      (let [{:keys [item accepted proj]} (nth log i)
            ctx {:w w :post proj :prev prev}
            a (adapt fmt ctx item)
            keep (fn [acc w] (cond-> acc worlds? (update :worlds conj w)))]
        (cond
          (:bump a)
          (let [c (:bump a)
                w1 (skip-to w (inc c))
                ds (if proj (diff proj (world->proj w1)) [])
                div? (or (< c (:next-id w)) (seq ds))]
            (recur (inc i) w1 (or proj prev)
                   (cond-> (keep (update acc :checked inc) w1)
                     div? (update :divergences conj {:commit i :item item :model-items [] :class :real
                                                     :n-diffs (count ds) :diffs (vec (take max-diffs ds)) :diffs-all ds}))))
          (:skip a)
          (let [w1 (if proj (resync proj) w)]
            (recur (inc i) w1 (or proj prev)
                   (-> acc (update-in [:skipped (:skip a)] (fnil inc 0)) (update :resyncs inc) (keep w1))))
          :else
          (let [main (:item a)
                cl (when (and main proj (not explicit-finally?)) (implicit-cleanup w proj))
                w (reduce (fn [w it] (:world (step-checked w it))) w cl)
                ex (when (and main proj (not explicit-exits?)) (implicit-exits w proj))
                w (reduce (fn [w it] (:world (step-checked w it))) w ex)
                wf (when (and main (not explicit-finally?)) (implicit-finally w proj main))
                w (or wf w)
                pre (when main (implicit-schedule w main))
                s0 (when pre (step-checked w pre))
                w0 (if s0 (:world s0) w)
                n0 (:next-id w0)
                w0 (if (and family? main) (align w0 main proj) w0)
                s1 (when main (step-checked w0 main))
                w1 (if s1 (:world s1) w0)
                m-acc (if main (:accepted s1) true)
                ;; a refused item carries no projection (oracle contract): only the accepted
                ;; flag is compared (a model refusal leaves its world unchanged, raw-refuse)
                ds (if proj (diff proj (world->proj w1)) [])
                dq (when (seq ds) (diff (world->proj (resync proj)) (world->proj w1)))
                ff (vec (concat (:failed-flags s0) (:failed-flags s1)))
                div? (or (not= accepted m-acc) (seq ds) (seq ff) (and s0 (not (:accepted s0))))
                acc (cond-> (keep (update (update acc (if main :checked :markers) inc)
                                          :skipped-ids + (- (:next-id w0) n0)) w1)
                      pre (update :implicit-schedules inc)
                      (seq cl) (update :implicit-cleanup (fnil + 0) (count cl))
                      (seq ex) (update :implicit-exits (fnil + 0) (count ex))
                      wf (update :implicit-finally inc)
                      div? (update :divergences conj
                                   {:commit i :item item :model-items (vec (remove nil? [pre main])) :implicit-finally (boolean wf)
                                    :accepted {:engine accepted :model m-acc}
                                    :implicit-schedule-refused (boolean (and s0 (not (:accepted s0))))
                                    :failed-flags ff :n-diffs (count ds) :diffs (vec (take max-diffs ds))
                                    ;; :granularity = only the slice-exit / resume lag differs
                                    :class (if (and (= accepted m-acc) (empty? ff) (empty? dq)
                                                    (not (and s0 (not (:accepted s0)))))
                                             :granularity :real)
                                    :n-diffs-quiesced (count dq) :diffs-quiesced (vec (take max-diffs dq))
                                    :diffs-all ds}))]
            (if (and div? resync-on-divergence? proj)
              (recur (inc i) (resync proj) proj (update acc :resyncs inc))
              (recur (inc i) w1 (or proj prev) acc))))))))))

(defn summary
  "The report map without the full diff lists."
  [res]
  (update res :divergences (partial mapv #(dissoc % :diffs-all))))

(defn run-file [path & opts] (summary (apply replay (read-log path) opts)))
