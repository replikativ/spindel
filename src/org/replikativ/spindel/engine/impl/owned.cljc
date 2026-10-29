(ns org.replikativ.spindel.engine.impl.owned
  "Owned-object CPS engine under construction. Canonical maps are diagnostic output,
  never the live representation. Supports the local reactive lifetime slice."
  (:refer-clojure :exclude [await assoc! dissoc! pop!])
  #?(:cljs (:require-macros [org.replikativ.spindel.engine.impl.owned :refer [a put locked each! each-copy! fields! with-activation]]))
  (:require [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.incremental.interval :as iv]))

#?(:clj (defonce ^:private activation-local (ThreadLocal.))
   :cljs (def ^:private active-frame nil))
(defn- current-activation []
  #?(:clj (.get ^ThreadLocal activation-local) :cljs active-frame))
#?(:clj
   (defmacro with-activation [frame & body]
     (if (:ns &env)
       `(let [previous# active-frame]
          (set! active-frame ~frame)
          (try ~@body (finally (set! active-frame previous#))))
       `(let [previous# (.get ^ThreadLocal activation-local)]
          (.set ^ThreadLocal activation-local ~frame)
          (try ~@body (finally (.set ^ThreadLocal activation-local previous#)))))))
#?(:clj
   (do
     (defmacro a [xs i]
       (if (:ns &env)
         `(cljs.core/aget ~xs ~i)
         (let [read `(let [^"[Ljava.lang.Object;" array# ~xs] (aget array# (int ~i)))]
           (if-let [tag (:tag (meta &form))]
             (let [value (with-meta (gensym "value") {:tag tag})]
               `(let [~value ~read] ~value))
             read))))
     (defmacro put [xs i value]
       (if (:ns &env) `(cljs.core/aset ~xs ~i ~value) `(let [^"[Ljava.lang.Object;" array# ~xs] (aset array# (int ~i) (clojure.lang.RT/box ~value)))))))
(defn- slots [n] #?(:clj (object-array n) :cljs (make-array n)))
#?(:cljs (deftype IDMap [buckets]))
#?(:cljs
   (deftype ValuesView [m]
     ;; Borrowed views stay internal; snapshots realize values under the gate.
     ISeqable
     (-seq [_]
       (when (pos? (.-size m)) (array-seq (js/Array.from (.values m)))))))
(defn- empty-native? [xs]
  #?(:clj (.isEmpty ^java.util.Collection xs)
     :cljs (cond (instance? ValuesView xs) (zero? (.-size (.-m xs)))
                 (array? xs) (zero? (.-length xs))
                 :else (zero? (.-size xs)))))
(defn- dict []
  #?(:clj (java.util.HashMap.)
     :cljs (let [m (js/Map.)]
             (set! (.-spindelValues m) (ValuesView. m))
             m)))
(defn- id-dict [] #?(:clj (dict) :cljs (IDMap. (js/Map.))))
(defn- find! [m k]
  #?(:clj (.get ^java.util.Map m k)
     :cljs (if (instance? IDMap m)
             (when-let [bucket (.get (.-buckets m) (hash k))]
               (loop [i 0]
                 (when (< i (.-length bucket))
                   (if (= k (aget bucket i)) (aget bucket (inc i)) (recur (+ i 2))))))
             (.get m k))))
(defn- assoc! [m k v]
  #?(:clj (.put ^java.util.Map m k v)
     :cljs (if (instance? IDMap m)
             (let [h (hash k) buckets (.-buckets m)]
               (if-let [bucket (.get buckets h)]
                 (loop [i 0]
                   (if (= i (.-length bucket)) (.push bucket k v)
                       (if (= k (aget bucket i)) (aset bucket (inc i) v) (recur (+ i 2)))))
                 (.set buckets h (array k v))))
             (.set m k v))) v)
(defn- dissoc! [m k]
  #?(:clj (.remove ^java.util.Map m k)
     :cljs (if (instance? IDMap m)
             (let [h (hash k) buckets (.-buckets m)]
               (when-let [bucket (.get buckets h)]
                 (loop [i 0]
                   (when (< i (.-length bucket))
                     (if (= k (aget bucket i))
                       (do (.splice bucket i 2)
                           (when (zero? (.-length bucket)) (.delete buckets h)))
                       (recur (+ i 2)))))))
             (.delete m k))))
(defn- members [] #?(:clj (java.util.HashSet.) :cljs (js/Set.)))
(def ^:private empty-members #?(:clj (java.util.Collections/emptySet) :cljs (js/Set.)))
(defn- clear-members! [s]
  (when-not (empty-native? s)
    #?(:clj (.clear ^java.util.Set s) :cljs (.clear s))))
(defn- add! [s x] #?(:clj (.add ^java.util.Set s x) :cljs (.add s x)))
(defn- remove! [s x] #?(:clj (.remove ^java.util.Set s x) :cljs (.delete s x)))
(defn- has? [s x] #?(:clj (.contains ^java.util.Set s x) :cljs (.has s x)))
(defn- items [s]
  #?(:clj (seq s)
     :cljs (if (instance? ValuesView s) (seq s) (array-seq (js/Array.from s)))))
(defn- values [m]
  #?(:clj (.values ^java.util.Map m)
     :cljs (if (instance? IDMap m)
             (let [result (array)]
               (.forEach (.-buckets m)
                         (fn [bucket] (loop [i 1]
                                        (when (< i (.-length bucket))
                                          (.push result (aget bucket i)) (recur (+ i 2))))))
               result)
             (.-spindelValues m))))
(defn- count! [s] #?(:clj (.size ^java.util.Collection s) :cljs (.-size s)))
(defn- queue [] #?(:clj (java.util.ArrayDeque.) :cljs (array)))
(defn- push! [q x] #?(:clj (.addLast ^java.util.ArrayDeque q x) :cljs (.push q x)))
(defn- pop! [q] #?(:clj (.pollFirst ^java.util.ArrayDeque q) :cljs (.shift q)))
(defn- queued? [q] #?(:clj (not (.isEmpty ^java.util.ArrayDeque q)) :cljs (pos? (.-length q))))

(def ^:private empty-array #?(:clj (object-array 0) :cljs (array)))
(defn- copy-items [xs]
  #?(:clj (.toArray ^java.util.Collection xs ^objects empty-array)
     :cljs (if (empty-native? xs) empty-array
               (js/Array.from (if (instance? ValuesView xs) (.values (.-m xs)) xs)))))
(defn- any! [xs pred]
  (when-not (empty-native? xs)
    #?(:clj (let [it (.iterator ^java.lang.Iterable xs)]
              (loop [] (when (.hasNext it)
                         (let [x (.next it)] (if (pred x) true (recur))))))
       :cljs (let [it (if (instance? ValuesView xs) (.values (.-m xs))
                          (js* "~{}[Symbol.iterator]()" xs))]
               (loop [] (let [entry (.next it)]
                          (when-not (.-done entry)
                            (if (pred (.-value entry)) true (recur)))))))))

#?(:clj
   (do
     (defmacro each! [[x xs] & body]
       (if (:ns &env)
         `(let [coll# ~xs]
            (when-not (empty-native? coll#)
              (.forEach (if (instance? ValuesView coll#) (.-m coll#) coll#)
                        (fn [~x] ~@body))))
         `(let [^java.util.Collection coll# ~xs]
            (when-not (.isEmpty coll#)
              (let [^java.util.Iterator it# (.iterator coll#)]
                (while (.hasNext it#) (let [~x (.next it#)] ~@body)))))))
     (defmacro fields! [[field fields] & body]
       `(do ~@(map (fn [value] `(let [~field ~value] ~@body)) fields)))
     (defmacro each-copy! [[x xs] & body]
       `(let [items# (copy-items ~xs)]
          (dotimes [i# (alength ^"[Ljava.lang.Object;" items#)]
            (let [~x (a items# i#)] ~@body))))))

;; Fixed layouts; graph links point to engine-owned objects in this local slice.
(def ^:const n-id 0) (def ^:const n-kind 1) (def ^:const n-owner 2)
(def ^:const n-creator 3) (def ^:const n-complete 4) (def ^:const n-kept 5)
(def ^:const n-value 6) (def ^:const n-tokens 7) (def ^:const n-order 8)
(def ^:const n-dirty 9) (def ^:const n-runs 10) (def ^:const n-dependents 11)
(def ^:const n-generation 12) (def ^:const n-body 13) (def ^:const n-rank 14)
(def ^:const n-ready 15) (def ^:const n-resume 16) (def ^:const n-work 17) (def ^:const n-current 18) (def ^:const n-pending-generation 19)
(def ^:const n-runtime 20) (def ^:const n-origin 21) (def ^:const n-source-world 22) (def ^:const n-created-by 23) (def ^:const n-creator-refs 24) (def ^:const n-creator-source 25)
(def ^:const r-node 0) (def ^:const r-gen 1) (def ^:const r-owner 2)
(def ^:const r-pred 3) (def ^:const r-status 4) (def ^:const r-created 5)
(def ^:const r-spawned 6) (def ^:const r-seq 7) (def ^:const r-obs 8)
(def ^:const r-owned 9) (def ^:const r-backlinks 10) (def ^:const r-childruns 11) (def ^:const r-physical 12) (def ^:const r-anchor 13) (def ^:const r-origin 14) (def ^:const r-source-world 15) (def ^:const r-wide 16) (def ^:const r-reactives 17) (def ^:const r-ancestors 18)
(def ^:const o-id 0) (def ^:const o-kind 1) (def ^:const o-debtor 2)
(def ^:const o-run 3) (def ^:const o-standing 4) (def ^:const o-resolve 5)
(def ^:const o-reject 6) (def ^:const o-order 7) (def ^:const o-slot 8)
(def ^:const o-success 9) (def ^:const o-failure 10) (def ^:const o-last 11)
(def ^:const o-live 12) (def ^:const o-value 13) (def ^:const o-host 14)
(def ^:const o-origin 15) (def ^:const o-source-world 16) (def ^:const o-creditor-generation 17) (def ^:const o-creditor-node 18)
(def ^:const t-id 0) (def ^:const t-spin 1) (def ^:const t-reachable 2)
(def ^:const t-touched 3) (def ^:const t-dropped 4) (def ^:const t-family 6)

(defrecord Handle [id token body])
(defrecord Source [id family])
(defrecord Ticket [id])
(defrecord Delivery [family world obligation])
(defrecord RootOwner [id])
(defrecord Failure [error])
(defrecord OwnedRuntime [gate nodes deliveries events hosts work ready draining counters audit tokens
                         serial thread world root family parent tickets lineage gc family-id owner-root
                         operations posts])
(def w [:w 0])
(def root [:root w])
(def cancelled ::cancelled)

#?(:clj
   (defmacro locked [rt & body]
     (if (:ns &env) `(do ~@body) `(locking (:gate ~rt) ~@body))))

(defn runtime
  ([] (runtime {}))
  ([{:keys [audit? world-id] :or {world-id w}}]
   (let [family (id-dict)
         rt (->OwnedRuntime
             #?(:clj (Object.) :cljs nil) (id-dict) (dict) (queue) (queue) (queue)
             #?(:clj (java.util.PriorityQueue.
                      11 (reify java.util.Comparator
                           (compare [_ x y]
                             (compare (long (a x n-rank)) (long (a y n-rank))))))
                :cljs (array))
             (atom false) (doto (slots 10) (put 9 (when audit? (queue))) (put 8 (members)) (put 0 (queue)) (put 4 (slots 32)) (put 5 (slots 8)) (put 1 0) (put 2 0) (put 3 (when audit? (id-dict))) (put 6 (members)) (put 7 (id-dict)))
             (when audit? (atom [])) (when audit? (members))
             (doto (slots 2) (put 0 0) (put 1 0)) (doto (slots 4) (put 3 world-id))
             world-id [:root world-id] family nil (id-dict)
             {:parent nil :root world-id :mode :root :cut nil :basis nil} (queue)
             #?(:clj (Object.) :cljs (js-obj)) (->RootOwner [:root world-id]) (dict) (queue))]
     (assoc! family world-id rt)
     rt)))

(defn- next-number! [rt i]
  (if (zero? i)
    (put (:serial rt) 0 (inc (long (a (:serial rt) 0))))
    (put (:counters rt) i (inc (long (a (:counters rt) i))))))
(defn- root-owner? [owner] (instance? RootOwner owner))
(defn- execution-runtime [rt] (if (current-activation) (a (current-activation) 0) rt))
(defn- parent-node [rt id]
  (loop [parent (:parent rt)]
    (when parent (or (find! (:nodes parent) id) (recur (:parent parent))))))

(defn- work-status? [status] (case status (:running :parked) true false))
(defn- active-status? [status] (case status (:running :parked :inherited :stale) true false))
(defn- resumable-status? [status] (case status (:parked :inherited) true false))
(defn- basis-status? [status] (case status (:completed :stale) true false))
(defn- fork-busy-status? [status] (case status (:running :unwinding :inherited) true false))

(defn- current [node] (a node n-current))
(defn- open-owner? [owner] (or (root-owner? owner) (and owner (not= :unwinding (a owner r-status)))))
(defn- mark! [rt node]
  (when (and node (not (a node n-work)))
    (put node n-work true) (push! (:work rt) node)))
(defn- reactive-kind? [kind] (or (= :track kind) (= :await-reactive kind)))
(defn- reactive? [run] (boolean (and run (pos? (long (or (a run r-reactives) 0))))))
(defn- reactive-delta! [run delta]
  (put run r-reactives (+ (long (or (a run r-reactives) 0)) (long delta))))
(declare drain! wanted? retire! cancel! reclaim! snapshot snapshot-family schedule! adopt! collect-token! map-value)

(defn- wanted? [node]
  (or (and (open-owner? (a node n-owner))
           (or (not= :spin (a node n-kind)) (not (a node n-complete)) (a node n-kept)))
      ;; A current non-work shell cannot hide an older active generation:
      ;; T7 retires predecessors and T11 retires its stale predecessor.
      (active-status? (some-> (current node) (a r-status)))
      (pos? (count! (a node n-dependents)))
      (any! (values (a node n-runs))
            (fn [run]
              (and (= :completed (a run r-status))
                   (or (pos? (count! (a run r-childruns)))
                       (any! (a run r-owned) #(and (not (identical? node %)) (wanted? %)))))))))

(defn- add-run! [run field member]
  (let [before (a run field)
        set (if (identical? before empty-members) (put run field (members)) before)]
    (add! set member)
    (when (> (count! set) 64) (put run r-wide true))))

(defn- owner! [rt node owner]
  (let [old (a node n-owner)]
    (when-not (identical? old owner)
      (when (and old (not (root-owner? old)))
        (remove! (a old r-owned) node) (mark! rt (a old r-node)))
      (put node n-owner owner)
      (when (and owner (not (root-owner? owner)))
        (add-run! owner r-owned node) (mark! rt (a owner r-node)))
      (mark! rt node))))

(defn- node! [rt id kind owner]
  (let [node (slots 26)]
    (put node n-id id) (put node n-runtime rt) (put node n-kind kind) (put node n-complete false)
    (put node n-kept false) (put node n-tokens (members)) (put node n-order 0)
    (put node n-created-by (members)) (put node n-creator-refs (dict))
    (put node n-runs (dict)) (put node n-dependents (members))
    (put node n-generation 0) (put node n-rank 0)
    (assoc! (:nodes rt) id node) (owner! rt node owner) node))

(defn- creator! [rt node creator]
  (let [old (a node n-creator)
        source (when creator (if (vector? creator) (find! (:nodes rt) (nth creator 0)) (a creator r-node)))]
    (when-not (identical? old creator)
      (doseq [[value source delta] [[old (a node n-creator-source) -1] [creator source 1]]
              :when (and value source)]
        (let [gen (if (vector? value) (nth value 1) (a value r-gen))
              refs (a source n-creator-refs) n (+ delta (long (or (find! refs gen) 0)))]
          (if (zero? n) (dissoc! refs gen) (assoc! refs gen n))
          (add! (a (:counters rt) 8) source)))
      (put node n-creator creator)
      (put node n-creator-source source))))

(defn- prune-ancestry! [rt]
  (each! [node (a (:counters rt) 8)]
         (each! [run (values (a node n-runs))]
                (each-copy! [gen (a run r-ancestors)]
                            (when-not (or (when-let [live (find! (a node n-runs) gen)] (not= :unwinding (a live r-status)))
                                          (find! (a node n-creator-refs) gen))
                              (remove! (a run r-ancestors) gen)))))
  #?(:clj (.clear ^java.util.Set (a (:counters rt) 8)) :cljs (.clear (a (:counters rt) 8))))

(defn- creation! [run node]
  (add-run! run r-created node) (add! (a node n-created-by) run))
(defn- uncreate! [run node]
  (remove! (a run r-created) node) (remove! (a node n-created-by) run))

(defn- end-ob! [rt ob]
  (when (a ob o-live)
    (put ob o-live false)
    (when (= :await-once (a ob o-kind))
      (dissoc! (:deliveries rt) (a ob o-id))
      (when-let [operation (find! (:operations rt) (a ob o-id))]
        (dissoc! (:operations rt) (a ob o-id))
        (if (= :consumed (a ob o-slot))
          (put operation 0 :settled)
          (do (put operation 0 :cancelled)
              (when-let [cancel (a operation 1)] (push! (:posts rt) (doto (slots 1) (put 0 cancel))))))
        (put operation 1 nil)))
    (when-let [run (a ob o-run)]
      (remove! (a run r-obs) ob)
      (when (reactive-kind? (a ob o-kind)) (reactive-delta! run -1))
      (mark! rt (a run r-node)))
    (when (= :await-once (a ob o-kind))
      (let [host (a ob o-host)]
        (when-let [waiters (find! (:tickets rt) host)]
          (remove! waiters ob)
          (when (zero? (count! waiters)) (dissoc! (:tickets rt) host)))))
    (when-let [node (a ob o-debtor)]
      (remove! (a node n-dependents) ob) (mark! rt node))))

(defn- reject-dependent! [rt ob]
  (if-let [run (a ob o-run)]
    (when (and (= :armed (a ob o-slot)) (= :parked (a run r-status)))
      (put run r-status :running) (put ob o-value cancelled)
      (schedule! rt (a run r-node) ob))
    (push! (:hosts rt) (doto (slots 2) (put 0 ob) (put 1 cancelled))))
  (end-ob! rt ob))

(defn- release-owned! [rt run]
  (each-copy! [node (a run r-owned)]
              (owner! rt node nil)
              (when (= :spin (a node n-kind)) (put node n-dirty true))
              (each-copy! [child (values (a node n-runs))]
                          (if (work-status? (a child r-status)) (cancel! rt child) (retire! rt child)))
              (each-copy! [ob (a node n-dependents)] (reject-dependent! rt ob))))

(defn- forget-run! [rt run]
  (let [node (a run r-node)]
    (dissoc! (a node n-runs) (a run r-gen))
    (add! (a (:counters rt) 8) node)
    (remove! (a (:counters rt) 6) run)
    (when (identical? run (current node))
      (put node n-current (last (sort-by #(a % r-gen) (values (a node n-runs))))))
    (mark! rt node)
    ;; Dead obligations carry their own creditor node/generation. They never
    ;; interpret a recycled run's identity when dispatching an old trigger.
    (fields! [field [r-created r-spawned r-obs r-owned r-backlinks r-childruns r-ancestors]]
             (if (a run r-wide)
               (put run field empty-members)
               (clear-members! (a run field))))
    (put run r-wide nil)
    (fields! [field [r-node r-gen r-owner r-pred r-status r-seq r-physical r-anchor r-origin r-source-world r-reactives]]
             (put run field nil))
    (let [pool (a (:counters rt) 0)]
      (when (< #?(:clj (.size ^java.util.ArrayDeque pool) :cljs (.-length pool)) 32)
        (push! pool run)))))

(defn- retire! [rt run]
  (when (and (has? (a (:counters rt) 6) run) (not= :unwinding (a run r-status)))
    (let [physical? (a run r-physical)
          anchor (when physical?
                   (loop [owner run chain []]
                     (if (root-owner? owner) (conj chain (:id owner) (:world rt))
                         (recur (a owner r-owner) (conj chain [(a (a owner r-node) n-id) (a owner r-gen)])))))]
      (each-copy! [ob (a run r-obs)] (end-ob! rt ob))
      (each-copy! [child (a run r-childruns)] (cancel! rt child))
      (release-owned! rt run)
      (each! [owner (a run r-backlinks)] (remove! (a owner r-spawned) run))
      (each! [child (a run r-spawned)] (remove! (a child r-backlinks) run))
      (each! [node (a run r-created)]
             (remove! (a node n-created-by) run)
             (when (identical? run (a node n-creator))
          ;; A surviving cache keeps the logical creator ID, not the old run's
          ;; mutable ownership graph.
               (if physical? (creator! rt node nil)
                   (put node n-creator [(a (a run r-node) n-id) (a run r-gen)]))))
      (when-let [owner (a run r-owner)]
        (when-not (root-owner? owner)
          (remove! (a owner r-childruns) run) (mark! rt (a owner r-node))))
      (if physical?
        (do (put run r-status :unwinding) (put run r-owner nil) (put run r-pred nil)
            (put run r-anchor anchor)
            (add! (a (:counters rt) 8) (a run r-node))
            (each! [successor (values (a (a run r-node) n-runs))]
                   (when (= (a run r-gen) (a successor r-pred)) (put successor r-pred nil)))
            (clear-members! (a run r-ancestors))
            (clear-members! (a run r-created))
            (clear-members! (a run r-spawned)))
        (forget-run! rt run))
      (mark! rt (a run r-node)))))

(defn- cancel! [rt run]
  (when (and (has? (a (:counters rt) 6) run) (not= :unwinding (a run r-status)))
    (let [node (a run r-node) current? (identical? run (current node))
          predecessor (find! (a node n-runs) (a run r-pred))]
      (retire! rt run)
      (when current?
        (each-copy! [ob (a node n-dependents)] (reject-dependent! rt ob))
        (when (and predecessor (= :stale (a predecessor r-status))) (retire! rt predecessor)))
      (put node n-dirty true))))

(defn- drop-node-events! [rt node]
  #?(:clj (.removeIf ^java.util.Collection (:events rt)
                     (reify java.util.function.Predicate
                       (test [_ event] (identical? node (a event 0)))))
     :cljs (loop [i (dec (.-length (:events rt)))]
             (when (>= i 0)
               (when (identical? node (a (aget (:events rt) i) 0)) (.splice (:events rt) i 1))
               (recur (dec i))))))

(defn- reclaim! [rt]
  (loop []
    (when-let [node (pop! (:work rt))]
      (put node n-work false)
      (when (and (identical? node (find! (:nodes rt) (a node n-id))) (not (wanted? node)))
        (when (and (= :spin (a node n-kind)) (a node n-complete))
          (each-copy! [run (values (a node n-runs))] (retire! rt run))
          (owner! rt node nil))
        (when-not (and (= :spin (a node n-kind)) (a node n-complete)
                       (pos? (count! (a node n-tokens))))
          (each-copy! [run (values (a node n-runs))] (retire! rt run))
          (each-copy! [creator (a node n-created-by)] (uncreate! creator node))
          (drop-node-events! rt node)
          (creator! rt node nil)
          (dissoc! (:nodes rt) (a node n-id))
          (put node n-body nil) (put node n-value nil) (put node n-resume nil)
          #?(:clj (.clear ^java.util.Set (a node n-tokens)) :cljs (.clear (a node n-tokens)))))
      (recur))))

(defn- audit-derived-state! [rt]
  (when-not (zero? (count! empty-members))
    (throw (ex-info "Shared empty membership was mutated" {})))
  (let [nodes (vec (values (:nodes rt)))
        sources (members)]
    (doseq [node nodes]
      (add! sources node)
      (when-let [source (a node n-creator-source)] (add! sources source)))
    (each! [source sources]
           (let [expected (frequencies
                           (for [node nodes :when (identical? source (a node n-creator-source))
                                 :let [creator (a node n-creator)]]
                             (if (vector? creator) (nth creator 1) (a creator r-gen))))
                 actual (map-value (a source n-creator-refs))]
             (when-not (= expected actual)
               (throw (ex-info "Creator-generation count mismatch" {:entity (a source n-id) :expected expected :actual actual}))))))

  (each! [node (values (:nodes rt))]
         (let [current-active (boolean (active-status? (some-> (current node) (a r-status))))
               any-active (boolean (any! (values (a node n-runs)) #(active-status? (a % r-status))))]
           (when-not (= current-active any-active)
             (throw (ex-info "Active-run projection mismatch" {:entity (a node n-id)})))))
  (each! [run (a (:counters rt) 6)]
         (let [actual (count (filter #(reactive-kind? (a % o-kind)) (items (a run r-obs))))]
           (when-not (= actual (or (a run r-reactives) 0))
             (throw (ex-info "Reactive-site count mismatch" {:run (a run r-gen) :expected actual :actual (a run r-reactives)}))))))

(defn- boundary! [rt action]
  (reclaim! rt)
  (prune-ancestry! rt)
  (when (:audit rt)
    (audit-derived-state! rt)
    (let [pending (a (:counters rt) 9)
          action (assoc action :fresh-runs (vec (items pending)))]
      #?(:clj (.clear ^java.util.ArrayDeque pending) :cljs (set! (.-length pending) 0))
      (swap! (:audit rt) conj [action (snapshot rt) (snapshot-family rt)]))))

(defn- touch! [rt node token]
  (when token (add! (a node n-tokens) token) (add! (a token t-touched) (:world rt))))
(defn- check-token! [rt token]
  (when (and token (not (identical? (:family-id rt) (a token t-family))))
    (throw (ex-info "Handle belongs to another runtime family" {:error :unknown-handle})))
  (when (and token (has? (a token t-dropped) (:world rt)))
    (throw (ex-info "Idle cache released" {:error :idle-cache-released}))))

(defn- check-running! [run]
  (when (and run (= :unwinding (a run r-status)))
    (throw (ex-info "Cancelled execution slice" {:error :cancelled}))))

(defn- predecessor-run? [previous caller]
  (when (and previous caller (not (root-owner? previous)))
    (let [id (if (vector? previous) (nth previous 0) (a (a previous r-node) n-id))
          gen (if (vector? previous) (nth previous 1) (a previous r-gen))]
      (and (= id (a (a caller r-node) n-id)) (has? (a caller r-ancestors) gen)))))

(defn signal [requested id value]
  (let [rt (execution-runtime requested)]
    (locked rt
            (let [run (when (current-activation) (a (current-activation) 1))
                  order (if run (put (current-activation) 2 (inc (long (a (current-activation) 2)))) 0)
                  _ (check-running! run)
                  old (find! (:nodes rt) id)
                  node (or old (node! rt id :signal (or run (:owner-root rt))))]
              (when-not (= :signal (a node n-kind)) (throw (ex-info "Source ID collision" {:id id})))
              (when (or (nil? old) (predecessor-run? (a node n-owner) run))
                (when-not old (put node n-value value))
                (owner! rt node (or run (:owner-root rt))) (put node n-order order)
                (when run (creation! run node)))
              (boundary! rt (when (:audit rt) (cond-> {:t :t02 :w (:world rt) :e id :value value}
                                                run (assoc :r [(a (a run r-node) n-id) (a run r-gen)] :order order))))
              (->Source id (:family-id rt))))))

#?(:clj (defonce ^:private handle-cleaner (java.lang.ref.Cleaner/create))
   :cljs (defonce ^:private handle-cleaner
           (js/FinalizationRegistry.
            (fn [held]
              (when-let [rt (.deref (aget held 0))]
                (collect-token! rt (aget held 1)))))))

(defn- arm-handle! [rt handle token]
  #?(:clj (let [runtime-ref (java.lang.ref.WeakReference. rt)]
            (put token 5 (.register ^java.lang.ref.Cleaner handle-cleaner handle
                                    (reify Runnable
                                      (run [_] (when-let [runtime (.get runtime-ref)]
                                                 (collect-token! runtime token)))))))
     :cljs (.register handle-cleaner handle (array (js/WeakRef. rt) token) token))
  handle)

(defn- collect-token! [rt token]
  (locked rt
          (when (a token t-reachable)
            (put token t-reachable false)
            (each! [world (a token t-touched)]
                   (when-let [target (find! (:family rt) world)]
                     (when (find! (:nodes target) (a token t-spin))
                       (push! (:gc rt) (doto (slots 2) (put 0 target) (put 1 token))))))
            (boundary! rt (when (:audit rt) {:t :t16 :tok (a token t-id)
                                             :notification-order (mapv #(-> (a % 0) :world)
                                                                       #?(:clj (seq (:gc rt)) :cljs (array-seq (:gc rt))))})))
          (loop []
            (when-let [notification (pop! (:gc rt))]
              (let [target (a notification 0) dead (a notification 1)]
                (when-let [node (find! (:nodes target) (a dead t-spin))]
                  (remove! (a node n-tokens) dead) (mark! target node))
                (boundary! target (when (:audit target) {:t :t17 :w (:world target) :e (a dead t-spin) :tok (a dead t-id)})))
              (recur))))
  (drain! rt))

(defn notify-unreachable!
  "Deterministic exercise of the host-finalization handoff for experiments."
  [rt handle]
  (when-not (identical? (:family-id rt) (a (:token handle) t-family))
    (throw (ex-info "Handle belongs to another runtime family" {:error :unknown-handle})))
  #?(:clj (.clean ^java.lang.ref.Cleaner$Cleanable (a (:token handle) 5))
     :cljs (do (.unregister handle-cleaner (:token handle)) (collect-token! rt (:token handle)))))

(defn make-spin [requested id body]
  (let [rt (execution-runtime requested)]
    (let [token (slots 7)]
      (put token t-family (:family-id rt))
      (put token t-id (random-uuid)) (put token t-spin id) (put token t-reachable true)
      (put token t-touched (members)) (put token t-dropped (members))
      (locked rt
              (when (:tokens rt) (add! (:tokens rt) token))
              (let [run (when (current-activation) (a (current-activation) 1))
                    order (if run (put (current-activation) 2 (inc (long (a (current-activation) 2)))) 0)
                    node (find! (:nodes rt) id)]
                (check-running! run)
                (when (and run (nil? node))
                  (let [node (node! rt id :spin run)]
                    (creator! rt node run) (put node n-kept (reactive? run)) (put node n-order order)
                    (creation! run node)))
                (when-let [node (find! (:nodes rt) id)]
                  (when (predecessor-run? (a node n-creator) run)
                    (adopt! rt node run)
                    (owner! rt node run) (creator! rt node run) (put node n-kept (reactive? run))
                    (put node n-order order) (creation! run node))
                  (touch! rt node token))
                (boundary! rt (when (:audit rt) (cond-> {:t :t01 :w (:world rt) :e id :tok (a token t-id)}
                                                  run (assoc :r [(a (a run r-node) n-id) (a run r-gen)] :order order))))))
      (arm-handle! rt (->Handle id token body) token))))

(defn track [& _] (throw (ex-info "track requires cspin" {})))
(defn await [& _] (throw (ex-info "await requires cspin" {})))
(defn park [& _] (throw (ex-info "park requires cspin" {})))
(defn await-host [& _] (throw (ex-info "await-host requires cspin" {})))
(defn ticket [id] (->Ticket id))
#?(:clj
   (do
     (defn- binding-sites [form vars]
       (cond
         (seq? form)
         (let [[op bindings & body] form]
           (cond
             (or (= 'quote op) (and (symbol? op) (= "cspin" (name op)))) form
             (#{'binding 'clojure.core/binding 'cljs.core/binding} op)
             (with-meta (list* op bindings (map #(binding-sites % (vec (distinct (concat vars (take-nth 2 bindings))))) body))
               (meta form))
             :else (with-meta (apply list (map #(binding-sites % vars) form))
                 ;; CLJS emits runtime metadata on fn expressions. Binding
                 ;; annotations belong to effect calls, never function values.
                     (cond-> (meta form)
                       (and (seq vars) (not (#{'fn 'fn* 'clojure.core/fn 'cljs.core/fn} (first form))))
                       (assoc ::binding-vars vars)))))
         (vector? form) (with-meta (mapv #(binding-sites % vars) form) (meta form))
         (map? form) (with-meta (into {} (map (fn [[k v]] [(binding-sites k vars) (binding-sites v vars)])) form) (meta form))
         :else form))
     (defn- bound-resume-form [vars k]
       (let [saved (mapv #(gensym (str (name %) "-saved")) vars)]
         `(let [~@(interleave saved vars)]
            (fn [value#]
              (binding [~@(interleave vars saved)]
                ;; The pump must stay inside the restored user scope. Direct
                ;; inline returns use raw continuations, so this is one frame
                ;; per resumed slice, never one nested frame per loop bounce.
                (cps/with-trampoline (cps/invoke-continuation ~k value#)))))))
     (defn- breakpoint [handler inline? ctx r e]
       (fn [args]
         (let [vars (::binding-vars (meta (:form ctx)))]
           (if (seq vars)
             (if inline?
               `(~handler ~@args ~r ~e ~(bound-resume-form vars r) ~(bound-resume-form vars e))
               `(~handler ~@args ~(bound-resume-form vars r) ~(bound-resume-form vars e)))
             `(~handler ~@args ~r ~e)))))
     (defn bp-track [ctx r e] (breakpoint `track-effect! true ctx r e))
     (defn bp-await [ctx r e] (breakpoint `await-effect! true ctx r e))
     (defn bp-park [ctx r e] (breakpoint `park-effect! false ctx r e))
     (defn bp-await-host [ctx r e] (breakpoint `await-host-effect! false ctx r e))
     (defmacro cspin [rt id & body]
       `(make-spin ~rt ~id ~((requiring-resolve 'org.replikativ.spindel.spin.cps/build-cps-fn)
                             (map #(binding-sites % []) body)
                             (merge cps/breakpoints
                                    {'org.replikativ.spindel.engine.impl.owned/track
                                     'org.replikativ.spindel.engine.impl.owned/bp-track
                                     'org.replikativ.spindel.engine.impl.owned/await
                                     'org.replikativ.spindel.engine.impl.owned/bp-await
                                     'org.replikativ.spindel.engine.impl.owned/park
                                     'org.replikativ.spindel.engine.impl.owned/bp-park
                                     'org.replikativ.spindel.engine.impl.owned/await-host
                                     'org.replikativ.spindel.engine.impl.owned/bp-await-host}) &env)))))

(defn- schedule! [rt node ob]
  (put node n-pending-generation (a (current node) r-gen))
  (let [previous (a node n-resume)]
    (when (or (nil? previous) (and ob (< (long (a ob o-order)) (long (a previous o-order)))))
      (put node n-resume ob)))
  (when-not (a node n-ready)
    (put node n-ready true)
    #?(:clj (.add ^java.util.PriorityQueue (:ready rt) node)
       :cljs (.push (:ready rt) node))))

(defn- run-slots! [rt]
  (or (pop! (a (:counters rt) 0))
      (let [run (slots 19)]
        (fields! [field [r-created r-spawned r-obs r-owned r-backlinks r-childruns r-ancestors]]
                 (put run field empty-members))
        run)))

(defn- start! [rt node owner reentry?]
  (when-not reentry? (put node n-resume nil))
  (each-copy! [inherited (values (a node n-runs))]
              (when (= :inherited (a inherited r-status)) (cancel! rt inherited)))
  (let [run (run-slots! rt)
        pred (current node)
        generation (put (:serial rt) 1 (inc (long (a (:serial rt) 1))))]
    (put node n-generation generation)
    (when (:audit rt)
      (assoc! (a (:counters rt) 3) (a node n-id) generation)
      (push! (a (:counters rt) 9) [(:world rt) (a node n-id) generation]))
    (put run r-reactives 0)
    (when (and pred (not= :unwinding (a pred r-status)))
      (each! [gen (a pred r-ancestors)] (add-run! run r-ancestors gen))
      (add-run! run r-ancestors (a pred r-gen)))
    (put run r-node node) (put run r-gen generation) (put run r-owner owner)
    (put run r-pred (when (and pred (not= :unwinding (a pred r-status))) (a pred r-gen))) (put run r-status :running)
    (put run r-seq (put (:counters rt) 1 (inc (max (long (a (:counters rt) 1)) (long (a (:counters rt) 2))))))
    (assoc! (a node n-runs) generation run)
    (add! (a (:counters rt) 6) run)
    (put node n-current run)
    (when-not (root-owner? owner)
      (add-run! owner r-spawned run) (add-run! run r-backlinks owner)
      (add-run! owner r-childruns run))
    (schedule! rt node nil)
    (mark! rt node) run))

(defn- ob! [rt kind debtor run order resolve reject]
  (let [ob (slots 19) id (a (:serial rt) 0)]
    (next-number! rt 0)
    (put ob o-id id) (put ob o-kind kind) (put ob o-debtor debtor) (put ob o-run run)
    (when run (put ob o-creditor-generation (a run r-gen)) (put ob o-creditor-node (a run r-node)))
    (put ob o-standing (case kind (:track :await-reactive :callback) true false))
    (put ob o-resolve resolve) (put ob o-reject reject) (put ob o-order order)
    (put ob o-slot (if (= kind :track) :consumed :armed)) (put ob o-live true)
    (when (= :await-once kind) (assoc! (:deliveries rt) id ob))
    (when run (add-run! run r-obs ob)
          (when (reactive-kind? kind) (reactive-delta! run 1)))
    (when debtor (add! (a debtor n-dependents) ob) (mark! rt debtor)) ob))

(defn- adopt! [rt node caller]
  (let [previous (a node n-owner)]
    (when (predecessor-run? previous caller)
      (when (identical? previous (a node n-creator))
        (creator! rt node caller) (put node n-kept (reactive? caller))
        (creation! caller node))
      (owner! rt node caller)
      (each! [run (values (a node n-runs))]
             (when (identical? previous (a run r-owner))
               (remove! (a previous r-childruns) run) (put run r-owner caller) (add-run! caller r-childruns run))))))

(defn- rank! [run debtor]
  (when debtor
    (let [node (a run r-node)]
      (put node n-rank (max (long (a node n-rank)) (inc (long (a debtor n-rank))))))))

(defn- register-track! [rt run order id resolve reject]
  (locked rt
          (check-running! run)
          (let [node (or (find! (:nodes rt) id)
                         (throw (ex-info "Foreign or released track is outside this slice" {:id id})))
                ob (ob! rt :track node run order resolve reject)]
            (put ob o-last (a node n-value)) (rank! run node)
            (boundary! rt (when (:audit rt) {:t :t05 :w (:world rt) :r [(a (a run r-node) n-id) (a run r-gen)]
                                             :kind :track :order order :debtor [:entity (:world rt) id]}))
            (a node n-value))))

(defn- track-id-effect! [id resolve reject resume-resolve resume-reject]
  (let [frame (current-activation) rt (a frame 0) run (a frame 1)
        order (put frame 2 (inc (long (a frame 2))))
        value (register-track! rt run order id resume-resolve resume-reject)]
    (cps/invoke-continuation resolve (iv/->Interval value value nil))))

(defn- check-source! [rt source]
  (when-not (identical? (:family-id rt) (:family source))
    (throw (ex-info "Source belongs to another runtime family" {:error :unknown-source}))))

(defn track-effect!
  ([source resolve reject]
   (check-source! (a (current-activation) 0) source)
   (track-id-effect! (:id source) resolve reject resolve reject))
  ([source resolve reject resume-resolve resume-reject]
   (check-source! (a (current-activation) 0) source)
   (track-id-effect! (:id source) resolve reject resume-resolve resume-reject)))

(defn- deliver-value! [resolve reject value]
  (cond
    (= cancelled value) (cps/invoke-continuation reject (ex-info "Cancelled" {:error :cancelled}))
    (instance? Failure value) (cps/invoke-continuation reject (:error value))
    :else (cps/invoke-continuation resolve value)))
(defn- deliver-cont! [ob value]
  (deliver-value! (a ob o-resolve) (a ob o-reject) value))

(defn- register-await! [rt run order id token body resolve reject]
  (locked rt
          (check-running! run)
          (check-token! rt token)
          (when (and (nil? (find! (:nodes rt) id)) (parent-node rt id))
            (throw (ex-info "Foreign await is outside this slice" {:id id})))
          (let [node (or (find! (:nodes rt) id) (node! rt id :spin run))]
            (put node n-body body)
            (adopt! rt node run)
            (when (and (not (a node n-complete)) (nil? (current node))) (start! rt node run false))
            (let [ob (ob! rt :await-reactive node run order resolve reject)]
              (put run r-status :parked) (touch! rt node token) (rank! run node)
              (boundary! rt (when (:audit rt) (cond-> {:t :t05 :w (:world rt) :r [(a (a run r-node) n-id) (a run r-gen)]
                                                       :kind :await-reactive :order order :debtor [:entity (:world rt) id]}
                                                token (assoc :tok (a token t-id)))))
              (when (and (a node n-complete)
                         (not (work-status? (some-> (current node) (a r-status)))))
                (put ob o-slot :consumed) (put run r-status :running) (put ob o-value (a node n-value))
                (boundary! rt (when (:audit rt) {:t :t06 :w (:world rt) :o [:o (a ob o-id)] :value (a node n-value)})))
              ob))))

(defn- await-id-effect! [id token body resolve reject resume-resolve resume-reject]
  (let [frame (current-activation) rt (a frame 0) run (a frame 1)
        order (put frame 2 (inc (long (a frame 2))))
        ob (register-await! rt run order id token body resume-resolve resume-reject)]
    (when (= :consumed (a ob o-slot)) (deliver-value! resolve reject (a ob o-value)))))

(defn await-effect!
  ([source resolve reject]
   (await-id-effect! (:id source) (:token source) (:body source) resolve reject resolve reject))
  ([source resolve reject resume-resolve resume-reject]
   (await-id-effect! (:id source) (:token source) (:body source) resolve reject resume-resolve resume-reject)))

(defn park-effect! [ticket resolve reject]
  (let [rt (a (current-activation) 0) run (a (current-activation) 1)
        order (put (current-activation) 2 (inc (long (a (current-activation) 2))))]
    (locked rt
            (check-running! run)
            (let [ob (ob! rt :await-once nil run order resolve reject)
                  waiters (or (find! (:tickets rt) (:id ticket))
                              (assoc! (:tickets rt) (:id ticket) (members)))]
              (put ob o-host (:id ticket)) (add! waiters ob)
              (put run r-status :parked)
              (boundary! rt (when (:audit rt) {:t :t05 :w (:world rt) :r [(a (a run r-node) n-id) (a run r-gen)]
                                               :kind :await-once :order order :debtor [:host (:id ticket)]}))))))

(defn pending-ticket [requested ticket]
  (let [rt (execution-runtime requested)]
    (locked rt
            (when-let [waiters (find! (:tickets rt) (:id ticket))]
              (when-let [ob (first (items waiters))]
                (->Delivery (:family-id rt) (:world rt) (a ob o-id)))))))

(defn resume-ticket! [requested delivery value]
  (let [rt (execution-runtime requested)]
    (when-not (and (identical? (:family-id rt) (:family delivery)) (= (:world rt) (:world delivery)))
      (throw (ex-info "Delivery belongs to a different runtime family or world" {:world (:world delivery)})))
    (locked rt
            (when-let [ob (find! (:deliveries rt) (:obligation delivery))]
              (let [run (a ob o-run)]
                (when (and (= :armed (a ob o-slot)) (resumable-status? (a run r-status)))
                  (end-ob! rt ob) (put run r-status :running) (put ob o-value value)
                  (schedule! rt (a run r-node) ob))))
            (boundary! rt (when (:audit rt) {:t :t06 :w (:world rt) :o [:o (:obligation delivery)] :value value})))
    (drain! rt)))

(defn- deliver-host! [rt delivery value]
  ;; A native callback owns this exact world/registration. In particular, a
  ;; synchronous callback must not redirect through some other active world.
  (locked rt
          (when-let [ob (find! (:deliveries rt) (:obligation delivery))]
            (let [run (a ob o-run)]
              (when (and (= :armed (a ob o-slot)) (resumable-status? (a run r-status)))
                (put ob o-slot :consumed)
                (end-ob! rt ob) (put run r-status :running) (put ob o-value value)
                (schedule! rt (a run r-node) ob))))
          (boundary! rt (when (:audit rt) {:t :t06 :w (:world rt) :o [:o (:obligation delivery)] :value value})))
  (drain! rt))

(defn- host-callback [rt delivery failed?]
  ;; A producer may keep a callback after cancellation/completion. That stale
  ;; capability must not keep the entire world and its application heap alive.
  (let [weak #?(:clj (java.lang.ref.WeakReference. rt) :cljs (js/WeakRef. rt))]
    (fn [value]
      (when-let [target #?(:clj (.get weak) :cljs (.deref weak))]
        (deliver-host! target delivery (if failed? (->Failure value) value))))))

(defn await-host-effect!
  "Park on a one-shot callback registration. `start` runs outside the gate with
  success/error callbacks and returns an optional cancellation function.
  Delivery is once-only and world/run fenced; cancellation is post-commit.
  Cancellation must synchronously detach the registration. Physical resources
  requiring asynchronous join need a separate lifetime owner/acknowledgement.
  Registrations require recovery support before they can be forked."
  [start resolve reject]
  (let [frame (current-activation) rt (a frame 0) run (a frame 1)
        order (put frame 2 (inc (long (a frame 2))))
        operation (slots 2)
        delivery (locked rt
                         (check-running! run)
                         (let [ob (ob! rt :await-once nil run order resolve reject)
                               host [:native (a ob o-id)]]
                           (put operation 0 :starting)
                           (assoc! (:operations rt) (a ob o-id) operation)
                           (put ob o-host host) (put run r-status :parked)
                           (boundary! rt (when (:audit rt) {:t :t05 :w (:world rt)
                                                            :r [(a (a run r-node) n-id) (a run r-gen)]
                                                            :kind :await-once :order order :debtor [:host host]}))
                           (->Delivery (:family-id rt) (:world rt) (a ob o-id))))]
    (when (locked rt (= :starting (a operation 0)))
      (let [cancel (try
                     (start (host-callback rt delivery false) (host-callback rt delivery true))
                     (catch #?(:clj Throwable :cljs :default) error
                       (deliver-host! rt delivery (->Failure error))
                       nil))]
        (locked rt
                (case (a operation 0)
                  :starting (do (put operation 0 :live) (put operation 1 cancel))
                  :cancelled (when cancel (push! (:posts rt) (doto (slots 1) (put 0 cancel))))
                  :settled nil))))
    nil))

(defn- complete! [requested run value]
  (let [rt (execution-runtime requested)]
    (locked rt
            (let [node (a run r-node)]
              (when (and (identical? run (current node)) (= :running (a run r-status)))
                (put node n-complete true) (put node n-dirty false) (put node n-value value)
                (put run r-status :completed)
                (push! (:events rt) (doto (slots 3) (put 0 node) (put 1 value) (put 2 (put (:counters rt) 2 (inc (max (long (a (:counters rt) 1)) (long (a (:counters rt) 2))))))))
                (each-copy! [previous (values (a node n-runs))]
                            (when (and (not (identical? previous run)) (basis-status? (a previous r-status)))
                              (retire! rt previous)))
                (mark! rt node))
              (boundary! rt (when (:audit rt) {:t :t07 :w (:world rt) :r [(a node n-id) (a run r-gen)] :value value}))))))

(defn- reenter! [rt node trigger]
  (let [previous (current node) work? (work-status? (a previous r-status))
        order (a trigger o-order)]
    (each-copy! [old (values (a node n-runs))]
                (when (= :stale (a old r-status)) (retire! rt old)))
    (let [run (start! rt node (a previous r-owner) true)]
      (when work?
        (put previous r-status :stale)
        (each-copy! [ob (a previous r-obs)]
                    (if (and (= :track (a ob o-kind)) (<= (long (a ob o-order)) (long order)))
                      (do (remove! (a previous r-obs) ob) (put ob o-run run) (reactive-delta! previous -1) (reactive-delta! run 1)
                          (put ob o-creditor-generation (a run r-gen))
                          (put ob o-creditor-node node) (add-run! run r-obs ob))
                      (end-ob! rt ob))))
      (each-copy! [child (a previous r-created)]
                  (when (< (long (a child n-order)) (long order))
                    (owner! rt child run)
                    (when (a child n-creator) (creator! rt child run))
                    (uncreate! previous child) (creation! run child)
                    (each! [cr (values (a child n-runs))]
                           (when (identical? previous (a cr r-owner))
                             (remove! (a previous r-childruns) cr) (put cr r-owner run) (add-run! run r-childruns cr)))))
      (schedule! rt node trigger))))

(defn- subscriber-buffer! [rt node]
  (let [n (count! (a node n-dependents))
        old (a (:counters rt) 4)
        buffer (if (< (alength ^objects old) n)
                 (put (:counters rt) 4 (slots (max n (* 2 (alength ^objects old))))) old)]
    #?(:clj (.toArray ^java.util.Collection (a node n-dependents) ^objects buffer)
       :cljs (let [i (volatile! 0)]
               (.forEach (a node n-dependents) (fn [ob] (put buffer @i ob) (vswap! i inc)))))
    n))

(defn- process-event! [rt event]
  (let [node (a event 0) value (a event 1)
        n (subscriber-buffer! rt node)
        dependents (a (:counters rt) 4)
        order (when (:audit rt) (mapv #(vector :o (a (a dependents %) o-id)) (range n)))]
    (try
      (dotimes [index n]
        (let [ob (a dependents index)]
          (if-let [run (a ob o-run)]
            (if (= :consumed (a ob o-slot))
              (reenter! rt (a ob o-creditor-node) ob)
              (when (and (a ob o-live) (= :parked (a run r-status)))
                (put ob o-slot :consumed) (put ob o-value value) (put run r-status :running)
                (schedule! rt (a ob o-creditor-node) ob)))
            (do (push! (:hosts rt) (doto (slots 2) (put 0 ob) (put 1 value)))
                (when (and (a node n-complete) (not (reactive? (current node)))) (end-ob! rt ob))))))
      (boundary! rt (when (:audit rt) {:t :t08 :w (:world rt) :e (a node n-id) :value value
                                       :delivery-order order}))
      (finally (dotimes [i n] (put dependents i nil))))))

(defn- poll-ready! [rt]
  #?(:clj (.poll ^java.util.PriorityQueue (:ready rt))
     :cljs (when (pos? (.-length (:ready rt)))
             (.sort (:ready rt) (fn [x y] (- (a x n-rank) (a y n-rank))))
             (.shift (:ready rt)))))

(declare drain!)
(defn- finish-slice! [rt run]
  (locked rt
          (put run r-physical false)
          (put (:thread rt) 0 nil)
          (when (= :unwinding (a run r-status)) (forget-run! rt run))
          (boundary! rt (when (:audit rt) {:t :t38 :th :engine}))))

(defn- claim-slice! [rt node]
  (locked rt
          (let [run (current node) ob (a node n-resume)]
            (put node n-ready false) (put node n-resume nil)
            (when (and run (= :running (a run r-status)) (= (a run r-gen) (a node n-pending-generation)))
              (when ob (rank! run (a ob o-debtor)))
              (put run r-physical true)
              (put (:thread rt) 0 run) (put (:thread rt) 1 true) (put (:thread rt) 2 (:world rt))
              (boundary! rt (when (:audit rt) {:t :slice-enter :w (:world rt) :r [(a node n-id) (a run r-gen)] :th :engine}))
              (let [frame (a (:counters rt) 5) debtor (when ob (a ob o-debtor))]
                (put frame 0 rt) (put frame 1 run) (put frame 2 (if ob (a ob o-order) -1))
                (put frame 3 ob) (put frame 4 (a node n-body))
                (put frame 5 (when debtor (a debtor n-value)))
                (put frame 6 (when debtor (a debtor n-body)))
                (put frame 7 (when ob (a ob o-last)))
                (when (and ob (= :track (a ob o-kind)) (identical? run (a ob o-run))
                           (= (a run r-gen) (a ob o-creditor-generation)))
                  (put ob o-last (a frame 5)))
                frame)))))

(defn- invoke-slice! [rt activation]
  (let [run (a activation 1) ob (a activation 3)]
    (if ob
      (let [moved? (and (identical? run (a ob o-run)) (= (a run r-gen) (a ob o-creditor-generation)))]
        (if (= :track (a ob o-kind))
          (if moved?
            (cps/invoke-continuation (a ob o-resolve) (iv/->Interval (a activation 7) (a activation 5) nil))
            (let [order (a ob o-order)
                  value (register-track! rt run order (a (a ob o-debtor) n-id) (a ob o-resolve) (a ob o-reject))]
              (put activation 2 order)
              (cps/invoke-continuation (a ob o-resolve) (iv/->Interval (a activation 7) value nil))))
          (if moved?
            (deliver-cont! ob (a ob o-value))
            (do (put activation 2 (dec (long (a ob o-order))))
                (await-id-effect! (a (a ob o-debtor) n-id) nil (a activation 6)
                                  (a ob o-resolve) (a ob o-reject) (a ob o-resolve) (a ob o-reject))))))
      ((a activation 4)
       (fn [value] (complete! rt (a (current-activation) 1) value))
       (fn [error] (complete! rt (a (current-activation) 1) (->Failure error)))))))

(defn- execute! [rt node]
  (when-let [activation (claim-slice! rt node)]
    (let [run (a activation 1) ob (a activation 3)]
      (try
        (with-activation activation
          (try (invoke-slice! rt activation)
               (catch #?(:clj Throwable :cljs :default) error
                 (try
                   (if ob (cps/invoke-continuation (a ob o-reject) error)
                       (complete! rt run (->Failure error)))
                   (catch #?(:clj Throwable :cljs :default) rejected
                     (complete! rt run (->Failure rejected)))))))
        (finally
          (finish-slice! rt run)
          (dotimes [i 8] (put activation i nil)))))))

(defn- next-dispatch! [rt]
  (locked rt
          (if-let [post (pop! (:posts rt))]
            post
            (if-let [event (pop! (:events rt))]
              (do (process-event! (a (a event 0) n-runtime) event) :event)
              (or (poll-ready! rt) (pop! (:hosts rt)))))))

(defn drain! [rt]
  (when (compare-and-set! (:draining rt) false true)
    (binding [cps/*in-trampoline* false]
      (let [failure
            (try
              (loop [failure nil]
                (if-let [entry (next-dispatch! rt)]
                  (if (and (not= :event entry) (= 1 (alength ^objects entry)))
                    ;; Logical cancellation is already committed. A failed
                    ;; detach must not strand other cancellation/delivery work.
                    (let [error (try ((a entry 0)) nil
                                     (catch #?(:clj Throwable :cljs :default) error error))]
                      (recur (or failure error)))
                    (do
                      (when-not (= :event entry)
                        (if (= 2 (alength ^objects entry))
                          (let [ob (a entry 0) value (a entry 1)]
                            (cond
                              (instance? Failure value) ((a ob o-failure) (:error value))
                              (= cancelled value) ((a ob o-failure) (ex-info "Cancelled" {}))
                              :else ((a ob o-success) value)))
                          (execute! (a entry n-runtime) entry)))
                      (recur failure)))
                  failure))
              (finally (reset! (:draining rt) false)))]
        (when (locked rt (or (queued? (:posts rt)) (queued? (:events rt)) (queued? (:hosts rt))
                             #?(:clj (not (.isEmpty ^java.util.PriorityQueue (:ready rt)))
                                :cljs (pos? (.-length (:ready rt))))))
          (drain! rt))
        (when failure (throw failure))))))

(defn observe! [requested handle success failure]
  (let [rt (execution-runtime requested)]
    (let [ob (locked rt
                     (check-token! rt (:token handle))
                     (when (and (nil? (find! (:nodes rt) (:id handle))) (parent-node rt (:id handle)))
                       (throw (ex-info "Foreign invocation is outside this slice" {:id (:id handle)})))
                     (let [node (or (find! (:nodes rt) (:id handle)) (node! rt (:id handle) :spin (:owner-root rt)))
                           cached? (and (a node n-complete) (not (a node n-dirty)) (not (work-status? (some-> (current node) (a r-status)))))]
                       (put node n-body (:body handle))
                       (when-not (a node n-owner) (owner! rt node (:owner-root rt)))
                       (touch! rt node (:token handle))
                       (when-not (or cached? (work-status? (some-> (current node) (a r-status)))) (start! rt node (:owner-root rt) false))
                       (let [ob (ob! rt :callback node nil 0 nil nil)]
                         (put ob o-success success) (put ob o-failure failure)
                         (when cached?
                           (push! (:hosts rt) (doto (slots 2) (put 0 ob) (put 1 (a node n-value))))
                           (when-not (reactive? (current node)) (end-ob! rt ob)))
                         (boundary! rt (when (:audit rt) {:t :t04 :w (:world rt) :e (:id handle) :tok (a (:token handle) t-id) :mode :callback}))
                         ob)))]
      (drain! rt)
      (fn []
        (locked rt
                (end-ob! rt ob)
                (boundary! rt (when (:audit rt) {:t :unsubscribe :w (:world rt) :o [:o (a ob o-id)]})))
        (drain! rt)))))

(defn- source-node! [rt source unwinding?]
  (let [node (find! (:nodes rt) (:id source))]
    (when-not (or (and unwinding? (nil? node))
                  (and node (= :signal (a node n-kind)) (or (a node n-owner) unwinding?)))
      (throw (ex-info "Released source" {:id (:id source)})))
    node))

(defn read-signal [requested source]
  (let [rt (execution-runtime requested)]
    (check-source! rt source)
    (locked rt (a (source-node! rt source false) n-value))))

(defn- write-source! [rt node source value]
  (when node
    (put node n-value value)
    (push! (:events rt) (doto (slots 3) (put 0 node) (put 1 value)
                              (put 2 (put (:counters rt) 2 (inc (max (long (a (:counters rt) 1))
                                                                     (long (a (:counters rt) 2)))))))))
  (boundary! rt (when (:audit rt) (cond-> {:t :signal-write :w (:world rt) :e (:id source) :value value}
                                    (current-activation) (assoc :th :engine)))))

(defn set-signal! [requested source value]
  (let [rt (execution-runtime requested)
        _ (check-source! rt source)
        unwinding? (and (current-activation) (= :unwinding (a (a (current-activation) 1) r-status)))]
    (locked rt
            (write-source! rt (source-node! rt source unwinding?) source value))
    (drain! rt)))

(defn compare-and-set-signal!
  "Identity CAS, including atom-style ABA semantics. The commit and reactive
  notification are one gated operation; a failed comparison changes nothing."
  [requested source old-value new-value]
  (let [rt (execution-runtime requested)]
    (check-source! rt source)
    (let [changed? (locked rt
                           (let [node (source-node! rt source false)]
                             (when (identical? old-value (a node n-value))
                               (write-source! rt node source new-value)
                               true)))]
      (when changed? (drain! rt))
      (boolean changed?))))

(defn swap-signal!
  "Apply f outside the ownership gate, retrying if its input changed."
  [requested source f & args]
  (loop []
    (let [old-value (read-signal requested source)
          new-value (if (seq args) (apply f old-value args) (f old-value))]
      (if (compare-and-set-signal! requested source old-value new-value)
        new-value
        (recur)))))

(defn cancel-spin! [requested handle]
  (let [rt (execution-runtime requested)]
    (locked rt
            (check-token! rt (:token handle))
            (let [node (find! (:nodes rt) (:id handle)) run (when node (current node))
                  id (when run [(a node n-id) (a run r-gen)])]
              (when run (cancel! rt run))
              (boundary! rt (when (:audit rt) {:t :t11 :w (:world rt) :r id}))))
    (drain! rt)))

(defn release-idle! [requested]
  (let [rt (execution-runtime requested)]
    (locked rt
            (doseq [node (vec (values (:nodes rt)))
                    :when (and (= :spin (a node n-kind)) (a node n-complete) (not (wanted? node)))]
              (doseq [token (items (a node n-tokens))] (add! (a token t-dropped) (:world rt)))
              #?(:clj (.clear ^java.util.Set (a node n-tokens)) :cljs (.clear (a node n-tokens)))
              (mark! rt node))
            (boundary! rt (when (:audit rt) {:t :t18 :w (:world rt)})))))

(defn- run-id [run]
  (when run (if (vector? run) run [(a (a run r-node) n-id) (a run r-gen)])))
(defn- owner-id [owner] (if (root-owner? owner) (:id owner) (run-id owner)))
(defn- map-value [m]
  #?(:clj (into {} m)
     :cljs (let [result (volatile! {})]
             (if (instance? IDMap m)
               (.forEach (.-buckets m)
                         (fn [bucket]
                           (loop [i 0]
                             (when (< i (.-length bucket))
                               (vswap! result assoc (aget bucket i) (aget bucket (inc i)))
                               (recur (+ i 2))))))
               (.forEach m (fn [value key] (vswap! result assoc key value))))
             @result)))

(defn- global-view [rt]
  (let [worlds (values (:family rt))]
    {:registry (set (map :world worlds)) :known-worlds (set (map :world worlds))
     :lineages (into {} (map (juxt :world :lineage) worlds))
     :caps (map-value (a (:counters rt) 7))
     :generation-clock (into {} (for [world worlds :let [clock (a (:counters world) 3)] :when clock [id n] (map-value clock)]
                                  [[(:world world) id] n]))}))

(defn- all-obligations [rt]
  ;; Internal graph links already own reactive registrations. Only ticket
  ;; deliveries need lookup by a host-visible registration number.
  (concat (mapcat #(items (a % r-obs)) (items (a (:counters rt) 6)))
          (for [node (values (:nodes rt)) ob (items (a node n-dependents))
                :when (nil? (a ob o-run))] ob)))

(defn snapshot [rt]
  (locked rt
          {:global (global-view rt) :lineage (:lineage rt) :root (:root rt) :status :live :admission :open :seal-seq nil
           :scopes {(:root rt) {:kind (if (:parent rt) :fork :world-root) :parent nil :status :open}}
           :pins #{} :fdeps #{} :releasing #{}
           :entities (into {} (for [node (values (:nodes rt))]
                                [(a node n-id)
                                 (cond-> {:kind (a node n-kind) :origin (or (a node n-origin) :created) :owner (owner-id (a node n-owner))
                                          :creator (run-id (a node n-creator)) :completed? (boolean (a node n-complete))
                                          :kept? (boolean (a node n-kept)) :result (a node n-value)
                                          :tokens (set (map #(a % t-id) (items (a node n-tokens)))) :key nil :order (a node n-order)}
                                   (some? (a node n-dirty)) (assoc :dirty? (a node n-dirty))
                                   (a node n-source-world) (assoc :source-world (a node n-source-world)))]))
           :runs (into {} (for [run (items (a (:counters rt) 6)) :let [node (a run r-node)]]
                            [(run-id run) (cond-> {:spin (a node n-id) :owner (owner-id (a run r-owner))
                                                   :pred (when-let [gen (a run r-pred)] [(a node n-id) gen])
                                                   :ancestors (set (map #(vector (a node n-id) %) (items (a run r-ancestors))))
                                                   :status (a run r-status) :seq (a run r-seq)
                                                   :creations (set (map #(a % n-id) (items (a run r-created))))
                                                   :spawned (set (map run-id (items (a run r-spawned))))}
                                            (= :unwinding (a run r-status)) (assoc :retired? true :anchor (a run r-anchor))
                                            (a run r-origin) (assoc :origin (a run r-origin) :source-world (a run r-source-world)))]))
           :obligations (into {} (for [ob (all-obligations rt)]
                                   [[:o (a ob o-id)]
                                    (cond-> {:kind (a ob o-kind) :debtor (if-let [debtor (a ob o-debtor)]
                                                                           [:entity (:world (a debtor n-runtime)) (a debtor n-id)]
                                                                           [:host (a ob o-host)])
                                             :creditor (if-let [run (a ob o-run)] [:run (:world rt) (run-id run)] [:host :caller])
                                             :standing? (a ob o-standing) :cont (when (a ob o-run) [:continuation [:o (a ob o-id)]])
                                             :token nil :order (a ob o-order) :slot (a ob o-slot)}
                                      (a ob o-run) (assoc :origin (or (a ob o-origin) :created))
                                      (a ob o-source-world) (assoc :source-world (a ob o-source-world))
                                      (nil? (a ob o-run)) (assoc :filter {:mode :local :origin (:world rt)}))]))
           :queue (mapv (fn [event] {:completion (a (a event 0) n-id) :debtor-world (:world rt) :value (a event 1) :seq (a event 2)})
                        (filter #(identical? rt (a (a % 0) n-runtime))
                                #?(:clj (seq (:events rt)) :cljs (array-seq (:events rt)))))
           :seq (a (:counters rt) 1)
           :serial (a (:serial rt) 0) :clock (a (:counters rt) 2)
           :threads (let [run (a (:thread rt) 0)]
                      (cond-> {:host {:world (a (:thread rt) 3) :scope nil :run nil :read-permits #{} :excl-permits []}}
                        (a (:thread rt) 1)
                        (assoc :engine (cond-> {:world (a (:thread rt) 2) :scope (run-id run) :run (run-id run) :executing? (boolean run)}
                                         run (assoc :obligation-world (a (:thread rt) 2))
                                         (= :unwinding (some-> run (a r-status))) (assoc :retired? true)))))
           :gc (mapv (fn [notification]
                       (let [target (a notification 0) token (a notification 1)]
                         {:t :t17 :w (:world target) :e (a token t-spin) :tok (a token t-id)}))
                     #?(:clj (seq (:gc rt)) :cljs (array-seq (:gc rt))))
           :handles (when (:tokens rt)
                      (into {} (for [token (items (:tokens rt))]
                                 [(a token t-id) {:spin (a token t-spin) :reachable? (a token t-reachable)
                                                  :touched (set (items (a token t-touched))) :dropped (set (items (a token t-dropped)))}])))}))

(defn fork-parked!
  "Prototype T19 for quiescent host-ticket bundles. Copies the ownership
  closure into independent mutable slots. Entity-debtor bundles and explicit
  scopes are refused until their cross-world retention path is implemented."
  [rt world]
  (locked rt
          (when (find! (:family rt) world)
            (throw (ex-info "World ID already used" {:world world})))
          (when (or (a (:thread rt) 0) (queued? (:events rt)))
            (throw (ex-info "Fork requires a parked boundary" {:world (:world rt)})))
          (let [copies (vec (filter #(= :parked (a % r-status)) (items (a (:counters rt) 6))))
                run-map (dict)
                selected (members)]
            (each! [run (a (:counters rt) 6)]
                   (when (fork-busy-status? (a run r-status))
                     (throw (ex-info "Fork requires a parked boundary" {:world (:world rt)}))))
            (doseq [run copies]
              (each! [ob (a run r-obs)]
                     (when (find! (:operations rt) (a ob o-id))
                       (throw (ex-info "Native operations require fork recovery" {:world (:world rt)})))
                     (when (or (a ob o-debtor) (not= :await-once (a ob o-kind)))
                       (throw (ex-info "Entity-debtor bundles are outside this slice" {:world (:world rt)}))))
              (add! selected (a run r-node)))
            (each! [node (values (:nodes rt))]
                   (when (some #(or (identical? % (a node n-owner)) (identical? % (a node n-creator))) copies)
                     (add! selected node)))
            (let [child (assoc (runtime {:audit? (boolean (:audit rt)) :world-id world})
                               :gate (:gate rt) :family (:family rt) :family-id (:family-id rt) :parent rt
                               :events (:events rt) :hosts (:hosts rt) :posts (:posts rt) :ready (:ready rt) :draining (:draining rt)
                               :serial (:serial rt) :thread (:thread rt) :gc (:gc rt)
                               :audit (:audit rt) :tokens (:tokens rt)
                               :lineage {:parent (:world rt) :root (get-in rt [:lineage :root])
                                         :mode :following :cut nil :basis nil})
                  node-map (dict)]
        ;; No old world version is pinned. The following child still retains
        ;; its live parent and code closures; only the parked ownership rows
        ;; are copied into child-owned mutable storage.
              (each! [node selected]
                     (let [copy (node! child (a node n-id) (a node n-kind) (:owner-root child))]
                       (assoc! node-map node copy)
                       (fields! [field [n-complete n-kept n-value n-order n-dirty n-body n-rank]]
                                (put copy field (a node field)))
                       (put copy n-origin :inherited) (put copy n-source-world (:world rt))
                       (each! [token (a node n-tokens)] (add! (a copy n-tokens) token))))
              (doseq [run copies]
                (let [copy (slots 19) node (find! node-map (a run r-node))]
                  (assoc! run-map run copy)
                  (put copy r-node node) (put copy r-gen (a run r-gen))
                  (put copy r-owner (:owner-root child)) (put copy r-pred (a run r-pred))
                  (put copy r-status :inherited) (put copy r-seq (a run r-seq)) (put copy r-reactives 0)
                  (put copy r-origin :inherited) (put copy r-source-world (:world rt))
                  (fields! [field [r-created r-spawned r-obs r-owned r-backlinks r-childruns r-ancestors]]
                           (put copy field empty-members))
                  (each! [gen (a run r-ancestors)] (add-run! copy r-ancestors gen))
                  (add! (a (:counters child) 8) node)
                  (assoc! (a node n-runs) (a copy r-gen) copy)
                  (when (or (nil? (current node)) (> (long (a copy r-gen)) (long (a (current node) r-gen))))
                    (put node n-current copy) (put node n-generation (a copy r-gen)))
                  (when (:audit child) (assoc! (a (:counters child) 3) (a node n-id) (a node n-generation)))
                  (add! (a (:counters child) 6) copy)))
              (each! [node selected]
                     (let [copy (find! node-map node)
                           creator (a node n-creator)]
                       (when-let [owner (find! run-map (a node n-owner))] (owner! child copy owner))
                       (creator! child copy (or (find! run-map creator) (run-id creator)))))
              (doseq [run copies]
                (let [copy (find! run-map run)]
                  (each! [created (a run r-created)]
                         (when-let [entity (find! node-map created)] (creation! copy entity)))
                  (each! [spawned (a run r-spawned)]
                         (when-let [descendant (find! run-map spawned)]
                           (add-run! copy r-spawned descendant) (add-run! descendant r-backlinks copy)))
                  (each! [ob (a run r-obs)]
                         (let [clone (slots 19)]
                           (fields! [field [o-id o-kind o-standing o-resolve o-reject o-order o-slot o-host]]
                                    (put clone field (a ob field)))
                           (put clone o-run copy) (put clone o-live true)
                           (put clone o-creditor-generation (a copy r-gen)) (put clone o-creditor-node (a copy r-node))
                           (put clone o-origin :inherited) (put clone o-source-world (:world rt))
                           (add-run! copy r-obs clone)
                           (when (reactive-kind? (a clone o-kind)) (reactive-delta! copy 1))
                           (when (= :await-once (a clone o-kind)) (assoc! (:deliveries child) (a clone o-id) clone))
                           (let [waiters (or (find! (:tickets child) (a clone o-host))
                                             (assoc! (:tickets child) (a clone o-host) (members)))]
                             (add! waiters clone))))))
              (reclaim! child)
              (prune-ancestry! child)
              (put (:counters child) 1 (a (:counters rt) 1))
              (put (:counters child) 7 (a (:counters rt) 7))
              (assoc! (a (:counters rt) 7) [:cap world]
                      {:world world :scope #{} :holder (:root rt) :disposition :open :published? true
                       :op nil :pred nil :successors [] :durable? false :bases {}})
              (assoc! (:family rt) world child)
              (node! rt [:fork world] :fork (:owner-root rt))
              (each! [node (values (:nodes child))]
                     (each! [token (a node n-tokens)] (add! (a token t-touched) world)))
              (boundary! rt (when (:audit rt) {:t :t19 :w (:world rt) :v world :k [:cap world]
                                               :scope (:root rt) :systems #{}}))
              child))))

(defn snapshot-family [rt]
  (locked rt
          (into {} (for [world (values (:family rt))] [(:world world) (snapshot world)]))))

(defn storage-stats [rt]
  (locked rt
          (let [runs (a (:counters rt) 6)
                pool (items (a (:counters rt) 0))]
            {:live-runs (count! runs)
             :ancestry-references (reduce + 0 (map #(count! (a % r-ancestors)) (items runs)))
             :pooled-runs (count pool)
             :pooled-references
             (reduce + 0 (for [run pool]
                           (+ (count (filter some? (map #(a run %) [r-node r-owner r-pred r-anchor])))
                              (reduce + 0 (map #(count! (a run %))
                                               [r-created r-spawned r-obs r-owned r-backlinks r-childruns r-ancestors])))))
             :orphan-creation-links
             (count (for [node (values (:nodes rt)) creator (items (a node n-created-by))
                          :when (not (has? runs creator))] creator))
             :scratch-references (count (filter some? (seq (a (:counters rt) 4))))})))
