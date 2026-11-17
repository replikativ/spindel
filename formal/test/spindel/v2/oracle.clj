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
            [clojure.java.io :as io]
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
            [spindel.v2.acts :as acts]
            [spindel.v2.ledger :as lg]
            [spindel.v2.sys :as sys]
            [spindel.v2.owned :as ow]))

;; ===========================================================================
;; Codes (state.clj)

(def scope-kinds [:root :run :explicit])
(def run-acts [:active :parked :done])
(def run-modes [:normal :unwinding])
(def edge-kinds {0 :wait 1 :dep 2 :observe 3 :savepoint})
(def edge-phases [:armed :fired])
(def act-modes [:one :all :any])
(def res-phases [:armed :fired :cancelling])
;; model codes (state.clj): 5 = rerun (never created), C0's link/stream are 6/7 (the engine's
;; SRC-LINK 5 / SRC-STREAM 6 are mapped through their keywords)
(def source-kinds [:signal :cell :deferred :mailbox :semaphore :rerun :link :stream])
(def res-kinds [:timer :external :offload :native :op])

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
                         :effect-index (:effect-index x) :finalizers (vec (repeat (count (filter en/fin-region (:finalizers x))) 0))
                         :resources (vec (:resources x))}))
     :sources (tbl (:sources w)
                   (fn [x] (let [k (kw-of source-kinds (:kind x))]
                             (cond-> {:owner (opt0 (:owner x)) :kind k
                                      ;; a stream's state is its tail (projected as :tail; engine nil)
                                      :state (when-not (= k :stream) (:state x))
                                      :version (:version x) :open (:open x) :handles (:handles x)}
                               ;; C0 links: the realizer (T14/T21 clear it at the realizer's cancel, as the
                               ;; engine's link-cancelled!; link-realize clears it), pull = a pull link
                               ;; still unrealized (or a computation's head, which the engine keeps for
                               ;; adoption), the next link
                               (= k :link)
                               (assoc :rtask (opt0 (:rtask x))
                                      :pull (and (zero? (:tail x))
                                                 (or (zero? (:version x))
                                                     (boolean (some (fn [c] (some #(= (:id x) (:id %)) (concat (:basis c) (:adopt-basis c))))
                                                                    (:comps w)))))
                                      :next (opt0 (:next x)))
                               (= k :stream) (assoc :tail (opt0 (:tail x)))))))
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
                               :handles (:handles c)
                               ;; C1 Q6: a demoted computation its run's cleanup entry keeps (§3.2)
                               :tomb (boolean (and (not (:idle c)) (nil? (:result c)) (zero? (:handles c))
                                                   (:run c) (contains? (:cleanup p) (:run c))))}))))
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
                                                {:queue (vec (:queue x))
                                                 ;; C0: a push link's `tail` is its stream (the stream whose tail it is,
                                                 ;; when unrealized; 0 otherwise: nothing reads it then); `fail` is not
                                                 ;; projected (the engine interns the failure box as the state)
                                                 :rtask (nil0 (:rtask x)) :next (nil0 (:next x))
                                                 :tail (or (:tail x)
                                                           (when (= :link (:kind x))
                                                             (some (fn [[sid y]] (when (= id (:tail y)) sid)) (:sources p)))
                                                           0)
                                                 :fail false})))
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
            :res (rows :res (fn [id z] (s/map->ResRow {:id id :owner (:owner z) :kind (code-of res-kinds (get {:savepoint :offload} (:kind z) (:kind z))) :at (:at z) :phase (code-of res-phases (:phase z))})))
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
                  only (re-entry point); the engine leaves 0, the model stores the site index
  :link-state     `:sources :state` of a realized link (C0): the engine interns its value
                  [v next-handle] (or the failure box) as one opaque value; the model keeps v
                  in `state` and next in `:next` (compared), the error in `state` with `fail`"
  {:mailbox-state true :wait-at true :link-state true})

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
    {:scopes (let [owns (set (concat (keep :owner (vals (:tasks p))) (keep :owner (vals (:sources p)))
                                     (keep :parent (vals (:scopes p)))))
                   used? (fn [id] (contains? owns id))]
               (into (sorted-map)
                     (map (fn [[id x]]
                            (let [x (apply dissoc (update x :kind (partial kw-of scope-kinds)) (ignored-fields :scopes))]
                              ;; a run scope that owns nothing reads as closed (engine session, C1): the
                              ;; engine materializes a run scope on first use (`run-scope!`), and one never
                              ;; materialized is nothing to close, the same as a closed, empty one
                              [id (cond-> x (and (= :run (:kind x)) (not (used? id))) (assoc :open false))])))
                     (:scopes p)))
     :comps (rows :comps #(-> % (update :basis set) (update :validity canon-validity)
                              (update :adoption canon-adoption) (update :inputs inputs-val)))
     :tasks (rows :tasks #(cond-> % (contains? % :inputs) (update :inputs inputs-val)))
     :runs (rows :runs #(-> % (update :finalizers count) (update :resources set)
                            (update :act (partial kw-of run-acts)) (update :mode (partial kw-of run-modes))))
     :sources (rows :sources #(cond-> (update % :kind (partial kw-of source-kinds))
                                (and (:mailbox-state *deviations*) (= :mailbox (kw-of source-kinds (:kind %))))
                                (dissoc :state)
                                (and (:link-state *deviations*) (= :link (kw-of source-kinds (:kind %)))
                                     (pos? (:version %)))
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

;; C1c stage B: the fork markers (the model's W-OWNED-N / W-NORMALIZE) are not compared row by row: the engine keeps
;; counts, not rows, and projects `:forks {}`. The sidecar's `:owned`/`:normalize` are compared instead
;; (check-observations).
(def row-tables [:scopes :comps :tasks :runs :sources :edges :acts :res :pubs])

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
  #{:create-source :track :arm :create-comp :spawn :await :complete :take :open-scope :create-link})

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
      ;; in the parent, whose run keeps its slice, but the count (C1c stage B): a marker c owned by the
      ;; run's current scope, in own-child!'s counting branch
      (= tag :fork) {:bump (second args) :fork-run (first args)}
      ;; C1c stage B (spindel.v2.owned): `[:owned-done s child]` and the drain `[:normalize]`
      (= tag :owned-done) {:owned-done (vec args)}
      (= tag :normalize) {:normalize true}
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
                   (when (pos? k) (mapcat (fn [_] [(item :finally-exit (:stamp x)) (item :finally-leave (:stamp x))]) (range k)))))
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

(defn stage-b-log? [log] (boolean (some #(#{:owned-done :normalize} (first (:item %))) log)))

(defn replay
  "Replays `log` through the model. Options: :format (default `log-format`), :strict? (no
  `pending-deviations`), :from (first commit index, default 0: start at
  `empty-world`, else re-sync from the projection of commit from - 1), :resync-on-divergence?
  (default false: lockstep, re-sync only after skipped items), :max-diffs (per divergence, 8),
  :init (the model world to start from, default `empty-world`: a fork's log starts from its
  parent's world at the fork commit), :family? (the log is of a world with forks: `align` the
  allocator before every item), :worlds? (keep the model world after every commit as :worlds),
  :unborn? (an instance's log: a `[:release-world]` before its activation, the first
  `:resource-fire`, is E4's release of an unborn instance, engine.clj `release-unborn`).
  Returns the summary map."
  [log & {:keys [format from resync-on-divergence? max-diffs strict? init family? worlds? unborn? owned?] :or {from 0 max-diffs 8}}]
  (binding [*deviations* (if strict? {} pending-deviations)]
  (let [fmt (or format (log-format log))
        ;; logs with `[:finally-enter st]`/`[:finally-exit st]` items (sample 4 on) need no
        ;; implicit finally regions or cleanup exits
        explicit-finally? (some #(#{:finally-enter :finally-exit} (first (:item %))) log)
        ;; logs with `[:slice-exit r]` items (Z#49, sample 7 on) need no implicit exits
        explicit-exits? (some #(= :slice-exit (first (:item %))) log)
        ;; C1c stage B: the inherited markers (W-NORMALIZE) are the markers of the world the log starts from
        norm0 (mapv :id (:forks (or init s/empty-world)))
        ;; a log of an engine with the stage B counts (it commits `[:owned-done]` / `[:normalize]` somewhere in the
        ;; family: `replay-family` passes it); older logs count nothing at the fork effect
        owned? (if (some? owned?) owned? (stage-b-log? log))]
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
          (and unborn? (= :release-world (first item))
               (not-any? #(= :resource-fire (first (:item %))) (take i log)))
          (let [w1 (cond-> (en/release-unborn w) (and family? proj) (skip-to (:next-id proj)))
                ds (if proj (diff proj (world->proj w1)) [])
                div? (or (not= accepted true) (seq ds))]
            (recur (inc i) w1 (or proj prev)
                   (cond-> (keep (update acc :checked inc) w1)
                     div? (update :divergences conj {:commit i :item item :model-items [:release-unborn] :class :real
                                                     :accepted {:engine accepted :model true}
                                                     :n-diffs (count ds) :diffs (vec (take max-diffs ds)) :diffs-all ds}))))
          (or (:owned-done a) (:normalize a))
          (let [w1 (cond-> (if-let [[sc c] (:owned-done a)] (ow/owned-done-world w sc c) (ow/drain-world w norm0))
                     ;; id-less items: the family counter (W-NEXT) moves with the relatives' allocations
                     (and family? proj) (skip-to (:next-id proj)))
                ds (if proj (diff proj (world->proj w1)) [])
                div? (or (not= accepted true) (seq ds))]
            (recur (inc i) w1 (or proj prev)
                   (cond-> (keep (update acc :checked inc) w1)
                     div? (update :divergences conj {:commit i :item item :model-items [] :class :real
                                                     :accepted {:engine accepted :model true}
                                                     :n-diffs (count ds) :diffs (vec (take max-diffs ds)) :diffs-all ds}))))
          (:bump a)
          (let [c (:bump a)
                rr (when-let [r (:fork-run a)] (first (s/run-find w r)))
                sc (when rr (en/cur-scope w rr))
                wc (skip-to w c)
                w1 (if (and owned? rr (ow/own-ok wc sc)) (ow/own-world wc sc c) (skip-to w (inc c)))
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
                      (seq cl) (update :implicit-cleanup (fnil + 0) (quot (count cl) 2))
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

;; ===========================================================================
;; C1 world completion (spec T21, Z#67): derived state, compared against the engine's
;; host-observation sidecar (`log-sample-N-observations.edn`: a vector of {:step :log-length {world
;; n} :obs {world {:complete? :released? :runs :kids :token}}} at settled host checkpoints).
;; The model keeps no counter, token or flag for it (the engine logs none):
;;   runs       the run rows (every unretired task and computation run, cleanup included)
;;   complete?  released and (an unborn instance, or no run left and every owned child world
;;              complete); a child world counts from its creation commit in its owner's log
;;   kids       the accepted children that are not complete (and not collected): exact (nil = 0). A
;;              child counts for its owner from its acceptance: at its creation, or, for a host fork
;;              into a busy owner, from the checkpoint `:accepted-from` (the owner's queued internal
;;              item: sample 23a); an instance from its activation
;; Tokens are the engine's exactly-once bookkeeping of the same relation and are not compared.

(defn read-observations [path]
  (let [f (io/file path)] (when (.exists f) (edn/read-string (slurp f)))))

(defn replay-family
  "Replays the worlds of a family. `spec`: {world {:log entries :from p :at i :kind k :owner o}}
  with kind :root (from empty-world), :fork-host / :instance (from world p's world after its
  commit i: the fork-host commit, the savepoint's arm), :fork (the fork effect `[:fork r c]` at
  commit i of p, `fork-child` of p's world before it); :owner (default p) is the world that owns
  it (completion). Returns {world {:res :init}}."
  [spec]
  (loop [todo (keys spec) out {}]
    (if-let [k (first (filter #(let [p (:from (spec %))] (or (nil? p) (contains? out p))) todo))]
      (let [{:keys [log at kind] parent :from} (spec k)
            pw (fn [n] (let [{:keys [res init]} (out parent)] (if (zero? n) init (nth (:worlds res) (dec n)))))
            init (case kind
                   :root s/empty-world
                   (:fork-host :instance) (pw (inc at))
                   :fork (:world (fork-child (pw at) (second (:item (nth (:log (spec parent)) at))))))
            res (replay log :family? true :init init :worlds? true :format :table :unborn? (= kind :instance)
                        :owned? (boolean (some (comp stage-b-log? :log) (vals spec))))]
        (recur (remove #{k} todo) (assoc out k {:res res :init init})))
      out)))


;; ---------------------------------------------------------------------------
;; C1c stage A (spec Z#70): the completion ledger and host joins, derived as well. Sidecar fields (when present):
;;   :tasks  {id {:done? :retired? :materialized? :srow-present? :complete?}}  every task seen at a checkpoint so far
;;   :scopes {id {:open? :present? :complete?}}                  every scope seen so far
;;   :pending-joins                                              live host joins: admitted, not yet delivered, not
;;                                                               withdrawn (engine #275; question 12)
;; Model side: spindel.v2.ledger (`task-complete`, `scope-complete`; the run scope of task k is k + 2) and the
;; layer-2 host joins of spindel.v2.sys (`join-ok`/`join-cell` admission, `deliver-cell`). A removed task or scope
;; reads as the ledger says: no task row = done and retired (its completion then needs only its run scope gone),
;; no scope row = complete. The engine materializes a run scope only when it immediately owns something (question
;; 11) and registers it then; the model creates it with the run. A task's run scope (k + 2) counts as seen, and
;; `srow-present?` as true, only once the sidecar reports the task `:materialized?` (engine #275); a run scope of no
;; task seen (a computation's) once it has owned something (a task, a source, a computation, a child scope or a
;; fork marker) in some model world so far. The model's `:materialized?` is that inference for the task's run
;; scope, compared with the sidecar's (question 11: the engine materializes a run scope only when it owns something).
;; Host joins are no log item: the family spec lists them as `:joins [[step target] ...]` per world, admitted before
;; checkpoint `step`, and withdrawals as `:withdraw [[step join-id] ...]` (join ids count the world's admitted joins
;; from 0), applied after that checkpoint's admissions and before its delivery.

(defn- owned-ids [w]
  (set (concat (map :owner (:tasks w)) (map :owner (:sources w)) (map :owner (:comps w))
               (map :parent (:scopes w)) (map :owner (:forks w)))))

(defn ledger-obs
  "The model's ledger observation of world `w` given `mat` (run scopes materialized so far) and the ids seen
  at earlier checkpoints `{:tasks #{} :scopes #{}}`: [obs seen']."
  [w mat seen]
  (let [scope-row (fn [s] (first (s/scope-find w s)))
        shown? (fn [x] (or (not= 1 (:kind x)) (contains? mat (:id x))))
        seen {:tasks (into (:tasks seen) (map :id (:tasks w)))
              :scopes (into (:scopes seen) (map :id (filter shown? (:scopes w))))}
        task (fn [k] (let [t (first (s/task-find w k))
                           sr (scope-row (lg/task-srow k))]
                       {:done? (if t (not= s/res-none (:tag (:result t))) true)
                        :retired? (if t (zero? (:run t)) true)
                        :srow-present? (boolean (and sr (contains? mat (:id sr))))
                        :complete? (lg/task-complete w k)}))
        scope (fn [x] (let [r (scope-row x)]
                        {:open? (boolean (and r (:open r))) :present? (some? r) :complete? (lg/scope-complete w x)}))]
    [{:tasks (into (sorted-map) (map (juxt identity task)) (:tasks seen))
      :scopes (into (sorted-map) (map (juxt identity scope)) (:scopes seen))}
     seen]))

(defn check-observations
  "Mismatches of the model's derived C1 state against the sidecar `obs` for the replayed family
  `fam` (replay-family of `spec`): a vector of {:step :world :field :engine :model}. C1c fields
  (`:tasks`, `:scopes`, `:pending-joins`) are compared when the sidecar has them."
  [spec fam obs]
  (let [step-idx (fn [s] (first (keep-indexed (fn [i o] (when (= s (:step o)) i)) obs)))
        at* (fn [k n] (let [{:keys [res init]} (fam k)] (if (zero? n) init (nth (:worlds res) (dec n)))))
        unborn-at? (fn [k n] (and (= :instance (:kind (spec k)))
                                  (not-any? #(= :resource-fire (first (:item %))) (take n (:log (spec k))))))
        joins (vec (mapcat (fn [[k x]] (map (fn [[step t]] [k step t]) (:joins x))) spec))
        inherited-mat (fn inherited-mat [k]
                        (let [{p :from at :at} (spec k)]
                          (if p
                            (into (inherited-mat p) (comp (map (partial at* p)) (mapcat owned-ids))
                                  (range (min (+ at 2) (inc (count (:log (spec p)))))))
                            #{})))
        withdrawals (vec (mapcat (fn [[k x]] (map (fn [[step j]] [k step j]) (:withdraw x))) spec))
        c1 (fn [idx log-length]
             (let [accepted? (fn [c] (let [a (:accepted-from (spec c))]
                                       (and (or (nil? a) (>= idx (step-idx a)))
                                            ;; an instance is accepted at its activation (activate!)
                                            (or (not= :instance (:kind (spec c)))
                                                (some #(= :resource-fire (first (:item %)))
                                                      (take (get log-length c 0) (:log (spec c))))))))
                   at (fn [k] (at* k (get log-length k 0)))
                   exists? (fn [k] (let [{:keys [at] parent :from} (spec k)]
                                     (or (nil? parent) (> (get log-length parent 0) at))))
                   unborn? (fn [k] (unborn-at? k (get log-length k 0)))
                   ;; a child collected (no log item: the spec names the first checkpoint after it, `:collected-at`)
                   collected? (fn [c] (when-let [s (:collected-at (spec c))] (>= idx (step-idx s))))
                   owner (fn [c] (let [x (spec c)] (get x :owner (:from x))))
                   children (fn [k] (filter #(and (= k (owner %)) (exists? %) (accepted? %)) (keys spec)))
                   complete? (fn complete? [k]
                               (let [w (at k)]
                                 (boolean (and (:released w)
                                               (or (unborn? k)
                                                   ;; C1c stage B (questions 15, 16): no marker (W-OWNED-N, W-NORMALIZE)
                                                   (and (empty? (:runs w)) (empty? (:forks w))
                                                        (every? #(or (collected? %) (complete? %)) (children k))))))))]
               {:at at :unborn? unborn? :complete? complete?
                :model (fn [k] {:runs (count (:runs (at k))) :released? (boolean (:released (at k)))
                                :complete? (complete? k)
                                :open-kids (count (remove #(or (collected? %) (complete? %)) (children k)))})}))
        ;; C1c: per checkpoint and world, the ledger observation and the pending host joins (state carried
        ;; across checkpoints: the ids seen, the run scopes materialized, the cell's joins)
        c1c (first
             (reduce
              (fn [[out st] [idx {:keys [step log-length] eo :obs}]]
                (let [{:keys [at unborn? complete?]} (c1 idx log-length)]
                  (reduce
                   (fn [[out st] k]
                     (let [n (get log-length k 0)
                           {:keys [seen mat smat js] :or {seen {:tasks #{} :scopes #{}} smat #{} js []}} (st k)
                           ;; C1c stage B (gap A): materialization is a row flag a fork copies (K-SROW; fork-effect!
                           ;; materializes the forking run's scope before the boundary): a world starts with what its
                           ;; source had owned up to the fork commit
                           mat (or mat (inherited-mat k))
                           mat (into mat (comp (map (partial at* k)) (mapcat owned-ids)) (range (inc n)))
                           ;; question 11 / #275: a task's run scope is materialized as the sidecar says
                           et (get-in eo [k :tasks])
                           smat (into smat (keep (fn [[t o]] (when (:materialized? o) (lg/task-srow t)))) et)
                           task-scope? (fn [x] (contains? (into (:tasks seen) (keys et)) (- x 2)))
                           w (at k)
                           [lo seen] (ledger-obs w (into smat (remove task-scope?) mat) seen)
                           ;; cross-check of question 11: the sidecar's :materialized? is the model's "owned something"
                           lo (update lo :tasks (fn [m] (into (sorted-map) (map (fn [[t o]] [t (assoc o :materialized? (contains? mat (lg/task-srow t)))])) m)))
                           cell (fn [js] (sys/->Cell w true 0 0 [] (unborn? k) 0 [] (complete? k) js []))
                           admitted (reduce (fn [c [_ _ t]] (if (sys/join-ok c t) (sys/join-cell c t) c))
                                            (cell js) (filter (fn [[jk js _]] (and (= jk k) (= js step))) joins))
                           withdrawn (reduce (fn [c [_ _ j]] (sys/withdraw-cell c j))
                                             admitted (filter (fn [[wk ws _]] (and (= wk k) (= ws step))) withdrawals))
                           js (vec (:joins (sys/deliver-cell withdrawn)))]
                       [(assoc out [idx k] (assoc lo :pending-joins (count (filter #(= sys/js-pending (:st %)) js))))
                        (assoc st k {:seen seen :mat mat :smat smat :js js})]))
                   [out st] (keys eo))))
              [{} {}] (map-indexed vector obs)))]
    (vec
     (for [[idx {:keys [step log-length] eo :obs}] (map-indexed vector obs)
           :let [{:keys [model at]} (c1 idx log-length)]
           [k e] eo
           :let [m (model k)
                 l (c1c [idx k])
                 ;; C1c stage B: the markers the world started with are its W-NORMALIZE (until `[:normalize]` drains
                 ;; them); the others are its own counts W-OWNED-N
                 mw (at k)
                 norm (set (map :id (:forks (:init (fam k)))))
                 mo (frequencies (keep #(when-not (norm (:id %)) (:owner %)) (:forks mw)))
                 mn (set (keep #(when (norm (:id %)) (:owner %)) (:forks mw)))]
           d (concat
              (for [f [:runs :released? :complete?] :when (not= (get e f) (get m f))]
                {:step step :world k :field f :engine (get e f) :model (get m f)})
              (when (not= (or (:kids e) 0) (:open-kids m))
                [{:step step :world k :field :kids :engine (:kids e) :model (:open-kids m)}])
              (for [t [:tasks :scopes] :when (contains? e t)
                    :let [et (get e t) mt (get l t)]
                    d (if (not= (set (keys et)) (set (keys mt)))
                        [{:step step :world k :field [t :ids] :engine (sort (keys et)) :model (sort (keys mt))}]
                        (for [[id er] et [f v] er :when (not= v (get-in mt [id f]))]
                          {:step step :world k :field [t id f] :engine v :model (get-in mt [id f])}))]
                d)
              (when (and (contains? e :pending-joins) (not= (:pending-joins e) (:pending-joins l)))
                [{:step step :world k :field :pending-joins :engine (:pending-joins e) :model (:pending-joins l)}])
              (when (and (contains? e :owned) (not= (into {} (:owned e)) mo))
                [{:step step :world k :field :owned :engine (:owned e) :model mo}])
              (when (and (contains? e :normalize) (not= (set (:normalize e)) mn))
                [{:step step :world k :field :normalize :engine (:normalize e) :model mn}]))]
       d))))
