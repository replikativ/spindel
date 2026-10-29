(ns org.replikativ.spindel.engine.impl.owned
  "Owned-object CPS engine under construction. Canonical maps are diagnostic output,
  never the live representation. Supports the local reactive lifetime slice."
  (:refer-clojure :exclude [await assoc! dissoc! pop!])
  #?(:cljs (:require-macros [org.replikativ.spindel.engine.impl.owned :refer [a put locked each! each-copy! fields! with-activation runtime-field]]))
  (:require [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.engine.protocols :as rtp]
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
#?(:cljs
   (deftype OwnedQueue [^:mutable buffer ^:mutable head ^:mutable length]
     Object
     (grow [_]
       (let [old buffer capacity (.-length old) next (doto (make-array (* 2 capacity)) (.fill nil))]
         (dotimes [i length] (aset next i (aget old (bit-and (+ head i) (dec capacity)))))
         (set! buffer next) (set! head 0)))
     (add [this value]
       (when (= length (.-length buffer)) (.grow this))
       (aset buffer (bit-and (+ head length) (dec (.-length buffer))) value)
       (set! length (inc length))
       this)
     (resetEmpty [_]
       (set! head 0)
       (when (> (.-length buffer) 256)
         (set! buffer (doto (make-array 16) (.fill nil)))))
     (poll [this]
       (when (pos? length)
         (let [value (aget buffer head)]
           (aset buffer head nil)
           (set! length (dec length))
           (if (zero? length) (.resetEmpty this)
               (set! head (bit-and (inc head) (dec (.-length buffer)))))
           value)))
     (removeAt [this index]
       (let [mask (dec (.-length buffer))]
         (loop [i index]
           (when (< i (dec length))
             (aset buffer (bit-and (+ head i) mask) (aget buffer (bit-and (+ head i 1) mask)))
             (recur (inc i))))
         (aset buffer (bit-and (+ head length -1) mask) nil)
         (set! length (dec length))
         (when (zero? length) (.resetEmpty this))))
     (remove [this value]
       (loop [i 0]
         (if (= i length) false
             (if (identical? value (aget buffer (bit-and (+ head i) (dec (.-length buffer)))))
               (do (.removeAt this i) true)
               (recur (inc i))))))
     (removeWhere [this pred]
       (let [n length mask (dec (.-length buffer))]
         (loop [read 0 write 0]
           (if (< read n)
             (let [value (aget buffer (bit-and (+ head read) mask))]
               (if (pred value) (recur (inc read) write)
                   (do (aset buffer (bit-and (+ head write) mask) value)
                       (recur (inc read) (inc write)))))
             (do (dotimes [i (- n write)] (aset buffer (bit-and (+ head write i) mask) nil))
                 (set! length write)
                 (when (zero? length) (.resetEmpty this)))))))
     (clear [this]
       (.fill buffer nil) (set! length 0) (.resetEmpty this))
     (toArray [_]
       (let [result (make-array length) mask (dec (.-length buffer))]
         (dotimes [i length] (aset result i (aget buffer (bit-and (+ head i) mask))))
         result))
     (forEach [_ visit]
       (dotimes [i length] (visit (aget buffer (bit-and (+ head i) (dec (.-length buffer)))))))
     (some [_ pred]
       (loop [i 0]
         (if (= i length) false
             (if (pred (aget buffer (bit-and (+ head i) (dec (.-length buffer))))) true
                 (recur (inc i))))))
     (capacity [_] (.-length buffer))
     (staleReferences [_]
       (let [mask (dec (.-length buffer))]
         (loop [i 0 n 0]
           (if (= i (.-length buffer)) n
               (recur (inc i) (if (and (>= (bit-and (- i head) mask) length)
                                       (some? (aget buffer i))) (inc n) n))))))))
(defn- empty-native? [xs]
  #?(:clj (.isEmpty ^java.util.Collection xs)
     :cljs (cond (instance? ValuesView xs) (zero? (.-size (.-m xs)))
                 (instance? OwnedQueue xs) (zero? (.-length xs))
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
#?(:cljs
   (defn- same-set-value? [x y]
     (or (identical? x y)
         (and (number? x) (number? y) (js/isNaN x) (js/isNaN y)))))

#?(:cljs
   (deftype InlineSet [^:mutable one ^:mutable two ^:mutable three ^:mutable size ^:mutable overflow]
     ;; Internal membership storage, not a public collection. Traversal borrows
     ;; a stable membership; destructive loops must use each-copy!, as on JVM.
     Object
     (has [_ value]
       (if overflow (.has overflow value)
           (boolean (or (and (> size 0) (same-set-value? value one))
                        (and (> size 1) (same-set-value? value two))
                        (and (> size 2) (same-set-value? value three))))))
     (add [this value]
       (if overflow
         (do (.add overflow value) (set! size (.-size overflow)))
         (when-not (.has this value)
           (let [value (if (identical? value 0) 0 value)]
             (case size
               0 (set! one value)
               1 (set! two value)
               2 (set! three value)
               3 (do (set! overflow (js/Set. (array one two three value)))
                     (set! one nil) (set! two nil) (set! three nil))))
           (set! size (inc size))))
       this)
     (delete [_ value]
       (if overflow
         (let [removed? (.delete overflow value)]
           (set! size (.-size overflow))
           (when (zero? size) (set! overflow nil))
           removed?)
         (cond
           (and (> size 0) (same-set-value? value one))
           (do (set! one two) (set! two three) (set! three nil) (set! size (dec size)) true)
           (and (> size 1) (same-set-value? value two))
           (do (set! two three) (set! three nil) (set! size (dec size)) true)
           (and (> size 2) (same-set-value? value three))
           (do (set! three nil) (set! size 2) true)
           :else false)))
     (clear [_]
       (set! one nil) (set! two nil) (set! three nil)
       (set! size 0) (set! overflow nil))
     (forEach [_ visit]
       (if overflow (.forEach overflow visit)
           (do (when (> size 0) (visit one))
               (when (> size 1) (visit two))
               (when (> size 2) (visit three)))))
     (copyInto [_ target]
       (if overflow
         (let [i (volatile! 0)]
           (.forEach overflow (fn [value] (aset target @i value) (vswap! i inc))))
         (do (when (> size 0) (aset target 0 one))
             (when (> size 1) (aset target 1 two))
             (when (> size 2) (aset target 2 three))))
       size)
     (some [_ pred]
       (if overflow
         (let [it (.values overflow)]
           (loop []
             (let [entry (.next it)]
               (if (.-done entry) false
                   (if (pred (.-value entry)) true (recur))))))
         (boolean (or (and (> size 0) (pred one))
                      (and (> size 1) (pred two))
                      (and (> size 2) (pred three))))))
     (toArray [_]
       (if overflow (js/Array.from overflow)
           (case size 0 (array) 1 (array one) 2 (array one two) 3 (array one two three))))))

(defn- members [] #?(:clj (java.util.HashSet.) :cljs (InlineSet. nil nil nil 0 nil)))
(def ^:private empty-members #?(:clj (java.util.Collections/emptySet) :cljs (js/Set.)))
(defn- clear-members! [s]
  (when-not (empty-native? s)
    #?(:clj (.clear ^java.util.Set s) :cljs (.clear s))))
(defn- add! [s x] #?(:clj (.add ^java.util.Set s x) :cljs (.add s x)))
(defn- remove! [s x] #?(:clj (.remove ^java.util.Set s x) :cljs (.delete s x)))
(defn- has? [s x] #?(:clj (.contains ^java.util.Set s x) :cljs (.has s x)))
(defn- items [s]
  #?(:clj (seq s)
     :cljs (if (instance? ValuesView s) (seq s)
               (array-seq (if (or (instance? InlineSet s) (instance? OwnedQueue s)) (.toArray s) (js/Array.from s))))))
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
(defn- queue [] #?(:clj (java.util.ArrayDeque.) :cljs (OwnedQueue. (doto (make-array 16) (.fill nil)) 0 0)))
(defn- push! [q x] #?(:clj (.addLast ^java.util.ArrayDeque q x) :cljs (.add q x)))
(defn- pop! [q] #?(:clj (.pollFirst ^java.util.ArrayDeque q) :cljs (.poll q)))
(defn- queued? [q] #?(:clj (not (.isEmpty ^java.util.ArrayDeque q)) :cljs (pos? (.-length q))))

(def ^:private empty-array #?(:clj (object-array 0) :cljs (array)))
(defn- copy-items [xs]
  #?(:clj (.toArray ^java.util.Collection xs ^objects empty-array)
     :cljs (cond (empty-native? xs) empty-array
                 (or (instance? InlineSet xs) (instance? OwnedQueue xs)) (.toArray xs)
                 :else (js/Array.from (if (instance? ValuesView xs) (.values (.-m xs)) xs)))))
(defn- any! [xs pred]
  (when-not (empty-native? xs)
    #?(:clj (let [it (.iterator ^java.lang.Iterable xs)]
              (loop [] (when (.hasNext it)
                         (let [x (.next it)] (if (pred x) true (recur))))))
       :cljs (if (or (instance? InlineSet xs) (instance? OwnedQueue xs)) (.some xs pred)
                 (let [it (if (instance? ValuesView xs) (.values (.-m xs))
                              (js* "~{}[Symbol.iterator]()" xs))]
                   (loop [] (let [entry (.next it)]
                              (when-not (.-done entry)
                                (if (pred (.-value entry)) true (recur))))))))))

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
(def ^:const n-source-event 26)
(def ^:const n-links 27) (def ^:const n-link-buffer 28) (def ^:const n-supporters 29)
(def ^:const n-graph-dirty 30) (def ^:const n-external-root 31)
(def ^:const r-node 0) (def ^:const r-gen 1) (def ^:const r-owner 2)
(def ^:const r-pred 3) (def ^:const r-status 4) (def ^:const r-created 5)
(def ^:const r-spawned 6) (def ^:const r-seq 7) (def ^:const r-obs 8)
(def ^:const r-owned 9) (def ^:const r-backlinks 10) (def ^:const r-childruns 11) (def ^:const r-physical 12) (def ^:const r-anchor 13) (def ^:const r-origin 14) (def ^:const r-source-world 15) (def ^:const r-wide 16) (def ^:const r-reactives 17) (def ^:const r-ancestors 18) (def ^:const r-validation-lost 19)
(def ^:const o-id 0) (def ^:const o-kind 1) (def ^:const o-debtor 2)
(def ^:const o-run 3) (def ^:const o-standing 4) (def ^:const o-resolve 5)
(def ^:const o-reject 6) (def ^:const o-order 7) (def ^:const o-slot 8)
;; Slot 9 is a callback for host creditors and a delivery error bit for run
;; creditors. These roles are disjoint; ordinary payloads never encode errors.
(def ^:const o-success 9) (def ^:const o-delivery-error 9) (def ^:const o-failure 10) (def ^:const o-last 11)
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

(defn- diagnostic-value [value failed?]
  (if failed? (->Failure value) value))
(defrecord RuntimeFamily [gate worlds host-tokens])
(declare read-application-state swap-application-state! cas-application-state!)
(defrecord OwnedRuntime [gate nodes deliveries events hosts work ready draining counters audit tokens
                         serial thread world root family parent tickets lineage gc family-id owner-root
                         operations posts home liveness extension-state]
  rtp/PWorldIdentity
  (world-identity [_] owner-root)
  rtp/PState
  (get-state [this path] (read-application-state this path))
  (swap-state! [this path f] (swap-application-state! this path f nil))
  (swap-state-args! [this path f args] (swap-application-state! this path f args))
  (cas-state! [this path old-value new-value] (cas-application-state! this path old-value new-value)))
(def w [:w 0])
(def root [:root w])
(def cancelled ::cancelled)

#?(:clj
   (defmacro runtime-field [rt field]
     ;; Fields are private to this implementation. Avoid keyword/protocol
     ;; lookup on JS while preserving ordinary record access during JVM REPL
     ;; reloads, where an older runtime can still be finishing a callback.
     (if (:ns &env)
       (list (symbol (str ".-" (name field)))
             (with-meta rt (assoc (meta rt) :tag 'org.replikativ.spindel.engine.impl.owned/OwnedRuntime)))
       (with-meta (list field rt) (meta &form)))))

#?(:clj
   (defmacro locked [rt & body]
     (if (:ns &env) `(do ~@body) `(locking (:gate ~rt) ~@body))))

(defn runtime
  ([] (runtime {}))
  ([{:keys [audit? record-audit? world-id] :or {record-audit? true world-id w}}]
   (let [family (id-dict) gate #?(:clj (Object.) :cljs nil)
         rt (->OwnedRuntime
             gate (id-dict) (dict) (queue) (queue) (queue)
             #?(:clj (java.util.PriorityQueue.
                      11 (reify java.util.Comparator
                           (compare [_ x y]
                             (compare (long (a x n-rank)) (long (a y n-rank))))))
                :cljs (array))
             (atom false) (doto (slots 10) (put 9 (when audit? (queue))) (put 8 (members)) (put 0 (queue)) (put 4 (slots 32)) (put 5 (slots 8)) (put 1 0) (put 2 0) (put 3 (when audit? (id-dict))) (put 6 (members)) (put 7 (id-dict)))
             (when audit? (atom (when record-audit? []))) (when audit? (members))
             (doto (slots 2) (put 0 0) (put 1 0)) (doto (slots 4) (put 3 world-id))
             world-id [:root world-id] family nil (id-dict)
             {:parent nil :root world-id :mode :root :cut nil :basis nil} (queue)
             #?(:clj (Object.) :cljs (js-obj)) (->RootOwner [:root world-id]) (dict) (queue)
             (->RuntimeFamily gate family #?(:clj (java.util.WeakHashMap.) :cljs (js/WeakMap.)))
             (doto (slots 6) (put 0 (queue)) (put 1 (members)) (put 2 (members))
                   (put 3 (members)) (put 4 (queue)) (put 5 (dict))) (atom {:values {} :shadowed #{} :map-groups #{}}))]
     (assoc! family world-id rt)
     rt)))

(defn- next-number! [rt i]
  (if (zero? i)
    (put (runtime-field rt :serial) 0 (inc (long (a (runtime-field rt :serial) 0))))
    (put (runtime-field rt :counters) i (inc (long (a (runtime-field rt :counters) i))))))
(defn- root-owner? [owner] (instance? RootOwner owner))
(defn- execution-runtime [rt] (if (current-activation) (a (current-activation) 0) rt))
(defn- parent-node [rt id]
  (loop [parent (runtime-field rt :parent)]
    (when parent (or (find! (:nodes parent) id) (recur (:parent parent))))))

(defn- work-status? [status] (case status (:running :parked) true false))
(defn- active-status? [status] (case status (:running :parked :inherited :stale) true false))
(defn- resumable-status? [status] (case status (:parked :inherited) true false))
(defn- basis-status? [status] (case status (:completed :stale) true false))
(defn- fork-busy-status? [status] (case status (:running :unwinding :inherited) true false))

(defn- current [node] (a node n-current))
(defn- open-owner? [owner] (or (root-owner? owner) (and owner (not= :unwinding (a owner r-status)))))
(defn- mark-graph! [rt node]
  (when (and node (not (a node n-graph-dirty)))
    (put node n-graph-dirty true) (push! (a (runtime-field rt :liveness) 0) node)))

(defn- mark! [rt node]
  (when (and node (not (a node n-work)))
    (put node n-work true) (push! (runtime-field rt :work) node)))

(defn- owner-node [owner]
  (when (and owner (not (root-owner? owner))) (a owner r-node)))

(defn- reactive-kind? [kind] (or (= :track kind) (= :await-reactive kind)))
(defn- reactive? [run] (boolean (and run (pos? (long (or (a run r-reactives) 0))))))
(defn- reactive-delta! [run delta]
  (put run r-reactives (+ (long (or (a run r-reactives) 0)) (long delta))))
(declare drain! wanted? retire! cancel! reclaim! snapshot snapshot-family schedule! adopt! collect-token! collect-home-token! map-value)

(defn- clear-live-set! [live slot]
  (let [before (a live slot)]
    (if (> (count! before) 64) (put live slot (members)) (clear-members! before))))

(defn- invalidate-liveness! [rt]
  (let [live (runtime-field rt :liveness)]
    (clear-live-set! live 1) (clear-live-set! live 2) (clear-live-set! live 3)))

(defn- owns-live-kind? [node]
  (or (not= :spin (a node n-kind)) (not (a node n-complete)) (a node n-kept)))

(defn- retain-link! [rt links target]
  (when (and target (identical? target (find! (runtime-field rt :nodes) (a target n-id))))
    (add! links target)))

(defn- reconcile-retention! [rt]
  (let [pending (a (runtime-field rt :liveness) 0)]
    (loop []
      (when-let [node (pop! pending)]
        (put node n-graph-dirty false)
        (let [before (a node n-links) next (a node n-link-buffer)
              present? (identical? node (find! (runtime-field rt :nodes) (a node n-id)))
              owner (a node n-owner)
              external? (boolean
                         (and present?
                              (or (and (root-owner? owner) (owns-live-kind? node))
                                  (any! (a node n-dependents) #(and (a % o-live) (nil? (a % o-run)))))))]
          (clear-members! next)
          (when present?
            (when (and owner (not (root-owner? owner)))
              (retain-link! rt next (a owner r-node)))
            (each! [run (values (a node n-runs))]
                   (when-not (= :unwinding (a run r-status))
                     (let [owner (a run r-owner)]
                       (when (and owner (not (root-owner? owner)))
                         (retain-link! rt next (a owner r-node))))
                     (each! [ob (a run r-obs)]
                            (when (a ob o-live) (retain-link! rt next (a ob o-debtor))))
                     (each! [child (a run r-owned)]
                            (when (and (open-owner? (a child n-owner)) (owns-live-kind? child))
                              (retain-link! rt next child))))))
          (when-not (= external? (boolean (a node n-external-root)))
            (put node n-external-root external?) (invalidate-liveness! rt))
          (if (and (= (count! before) (count! next))
                   (not (any! before #(not (has? next %)))))
            (clear-members! next)
            (do
              (invalidate-liveness! rt)
              (each! [target before]
                     (when-not (has? next target)
                       (let [supporters (a target n-supporters)]
                         (remove! supporters node)
                         ;; Drop backing storage after wide fan-out contracts.
                         (when (or (zero? (count! supporters)) (= 64 (count! supporters)))
                           (let [small (members)]
                             (each! [entry supporters] (add! small entry))
                             (put target n-supporters small))))))
              (each! [target next]
                     (when-not (has? before target) (add! (a target n-supporters) node)))
              (if (and (> (count! before) 64) (<= (count! next) 64))
                (let [small (members)]
                  (each! [target next] (add! small target))
                  (put node n-links small) (put node n-link-buffer (members)))
                (do (put node n-links next) (put node n-link-buffer before)
                    (clear-members! before)))))
          (when-not present? (put node n-supporters (members))))
        (recur)))))

(defn- dict-has? [m key]
  #?(:clj (.containsKey ^java.util.Map m key) :cljs (.has m key)))

(defn- remember-live-path! [cache parents node]
  (loop [node node]
    (when node (add! cache node) (recur (find! parents node)))))

(defn- find-live-root! [rt node]
  (let [live (runtime-field rt :liveness) external (a live 1) work (a live 2) absent (a live 3)
        pending (a live 4) parents (a live 5)]
    (push! pending node) (assoc! parents node nil)
    (try
      (loop []
        (if-let [candidate (pop! pending)]
          (cond
            (or (a candidate n-external-root) (has? external candidate))
            (do (remember-live-path! external parents candidate) true)
            (or (active-status? (some-> (current candidate) (a r-status))) (has? work candidate))
            (do (remember-live-path! work parents candidate) true)
            (has? absent candidate) (recur)
            :else
            (do (each! [supporter (a candidate n-supporters)]
                       (when-not (dict-has? parents supporter)
                         (assoc! parents supporter candidate) (push! pending supporter)))
                (recur)))
          (do
            (doseq [candidate #?(:clj (.keySet ^java.util.Map parents)
                                 :cljs (array-seq (js/Array.from (.keys parents))))]
              (add! absent candidate))
            false)))
      (finally
        #?(:clj (.clear ^java.util.ArrayDeque pending) :cljs (.clear pending))
        (if (> #?(:clj (.size ^java.util.Map parents) :cljs (.-size parents)) 64)
          (put live 5 (dict))
          #?(:clj (.clear ^java.util.Map parents) :cljs (.clear parents)))))))

(defn- wanted? [node]
  (let [rt (a node n-runtime) live (runtime-field rt :liveness)]
    (reconcile-retention! rt)
    (or (a node n-external-root)
        (active-status? (some-> (current node) (a r-status)))
        (has? (a live 1) node) (has? (a live 2) node)
        (and (not (has? (a live 3) node)) (find-live-root! rt node)))))

(defn- add-run! [run field member]
  (let [before (a run field)
        set (if (identical? before empty-members) (put run field (members)) before)]
    (add! set member)
    (when (> (count! set) 64) (put run r-wide true))))

(defn- owner! [rt node owner]
  (let [old (a node n-owner)]
    (when-not (identical? old owner)
      (when (or (not= (root-owner? old) (root-owner? owner))
                (not (identical? (owner-node old) (owner-node owner)))
                (not= (boolean (open-owner? old)) (boolean (open-owner? owner))))
        (mark-graph! rt node) (mark-graph! rt (owner-node old)) (mark-graph! rt (owner-node owner)))
      (when-let [parent (owner-node old)]
        (remove! (a old r-owned) node) (mark! rt parent))
      (put node n-owner owner)
      (when-let [parent (owner-node owner)]
        (add-run! owner r-owned node) (mark! rt parent))
      (mark! rt node))))

(defn- kept! [rt node value]
  (when-not (= (boolean value) (boolean (a node n-kept)))
    (mark-graph! rt node) (mark-graph! rt (owner-node (a node n-owner))))
  (put node n-kept value))

(defn- node! [rt id kind owner]
  (let [node (slots 32)]
    (put node n-id id) (put node n-runtime rt) (put node n-kind kind) (put node n-complete false)
    (put node n-kept false) (put node n-tokens (members)) (put node n-order 0)
    (put node n-created-by (members)) (put node n-creator-refs (dict))
    (put node n-runs (dict)) (put node n-dependents (members))
    (put node n-links (members)) (put node n-link-buffer (members)) (put node n-supporters (members))
    (put node n-generation 0) (put node n-rank 0)
    (assoc! (runtime-field rt :nodes) id node) (mark-graph! rt node) (owner! rt node owner) node))

(defn- creator! [rt node creator]
  (let [old (a node n-creator)
        source (when creator (if (vector? creator) (find! (runtime-field rt :nodes) (nth creator 0)) (a creator r-node)))]
    (when-not (identical? old creator)
      (doseq [[value source delta] [[old (a node n-creator-source) -1] [creator source 1]]
              :when (and value source)]
        (let [gen (if (vector? value) (nth value 1) (a value r-gen))
              refs (a source n-creator-refs) n (+ delta (long (or (find! refs gen) 0)))]
          (if (zero? n) (dissoc! refs gen) (assoc! refs gen n))
          (add! (a (runtime-field rt :counters) 8) source)))
      (put node n-creator creator)
      (put node n-creator-source source))))

(defn- prune-ancestry! [rt]
  (each! [node (a (runtime-field rt :counters) 8)]
         (each! [run (values (a node n-runs))]
                (each-copy! [gen (a run r-ancestors)]
                            (when-not (or (when-let [live (find! (a node n-runs) gen)] (not= :unwinding (a live r-status)))
                                          (find! (a node n-creator-refs) gen))
                              (remove! (a run r-ancestors) gen)))))
  (clear-members! (a (runtime-field rt :counters) 8)))

(defn- creation! [run node]
  (add-run! run r-created node) (add! (a node n-created-by) run))
(defn- uncreate! [run node]
  (remove! (a run r-created) node) (remove! (a node n-created-by) run))

(defn- end-ob! [rt ob]
  (when (a ob o-live)
    (put ob o-live false)
    (when (= :await-once (a ob o-kind))
      (dissoc! (runtime-field rt :deliveries) (a ob o-id))
      (when-let [operation (find! (runtime-field rt :operations) (a ob o-id))]
        (dissoc! (runtime-field rt :operations) (a ob o-id))
        (if (= :consumed (a ob o-slot))
          (put operation 0 :settled)
          (do (put operation 0 :cancelled)
              (when-let [cancel (a operation 1)] (push! (runtime-field rt :posts) (doto (slots 1) (put 0 cancel))))))
        (put operation 1 nil)))
    (when-let [run (a ob o-run)]
      (remove! (a run r-obs) ob)
      (when (reactive-kind? (a ob o-kind)) (reactive-delta! run -1))
      (mark! rt (a run r-node)))
    (when (= :await-once (a ob o-kind))
      (let [host (a ob o-host)]
        (when-let [waiters (find! (runtime-field rt :tickets) host)]
          (remove! waiters ob)
          (when (zero? (count! waiters)) (dissoc! (runtime-field rt :tickets) host)))))
    (when-let [node (a ob o-debtor)]
      (remove! (a node n-dependents) ob) (mark! rt node)
      (if-let [creditor (a ob o-creditor-node)]
        (when-not
         ;; Search the smaller adjacency. A shared source can have thousands
         ;; of dependents while each creditor has only one outgoing edge.
         (if (and (current creditor)
                  (< (count! (a (current creditor) r-obs)) (count! (a node n-dependents))))
           (any! (values (a creditor n-runs))
                 (fn [run]
                   (any! (a run r-obs) #(and (a % o-live) (identical? node (a % o-debtor))))))
           (any! (a node n-dependents)
                 #(and (a % o-live) (identical? creditor (a % o-creditor-node)))))
          (mark-graph! rt creditor))
        (when-not (any! (a node n-dependents) #(and (a % o-live) (nil? (a % o-run))))
          (mark-graph! rt node))))))

(defn- reject-dependent! [rt ob]
  (if-let [run (a ob o-run)]
    (do
      (when (and (= :consumed (a ob o-slot)) (= :await-reactive (a ob o-kind))
                 (#{:running :parked :inherited :completed} (a run r-status)) (identical? run (current (a run r-node))))
        (put run r-validation-lost true)
        (when (a (a run r-node) n-complete) (put (a run r-node) n-dirty true)))
      (when (and (= :armed (a ob o-slot)) (= :parked (a run r-status)))
        (put run r-status :running)
        (put ob o-value (ex-info "Cancelled" {:error :cancelled}))
        (put ob o-delivery-error true)
        (schedule! rt (a run r-node) ob)))
    (push! (runtime-field rt :hosts)
           (doto (slots 2) (put 0 (a ob o-failure)) (put 1 (ex-info "Cancelled" {})))))
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
    (add! (a (runtime-field rt :counters) 8) node)
    (remove! (a (runtime-field rt :counters) 6) run)
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
    (fields! [field [r-node r-gen r-owner r-pred r-status r-seq r-physical r-anchor r-origin r-source-world r-reactives r-validation-lost]]
             (put run field nil))
    (let [pool (a (runtime-field rt :counters) 0)]
      (when (< #?(:clj (.size ^java.util.ArrayDeque pool) :cljs (.-length pool)) 32)
        (push! pool run)))))

(defn- retire! [rt run]
  (when (and (has? (a (runtime-field rt :counters) 6) run) (not= :unwinding (a run r-status)))
    (let [node (a run r-node) physical? (a run r-physical)
          anchor (when physical?
                   (loop [owner run chain []]
                     (if (root-owner? owner) (conj chain (:id owner) (runtime-field rt :world))
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
          (let [parent (a owner r-node)]
            (when (and (not (identical? parent (owner-node (a node n-owner))))
                       (not (any! (values (a node n-runs))
                                  #(and (not (identical? run %)) (not= :unwinding (a % r-status))
                                        (identical? parent (owner-node (a % r-owner)))))))
              (mark-graph! rt node)))
          (remove! (a owner r-childruns) run) (mark! rt (a owner r-node))))
      (if physical?
        (do (put run r-status :unwinding) (put run r-owner nil) (put run r-pred nil)
            (put run r-anchor anchor)
            (add! (a (runtime-field rt :counters) 8) (a run r-node))
            (each! [successor (values (a (a run r-node) n-runs))]
                   (when (= (a run r-gen) (a successor r-pred)) (put successor r-pred nil)))
            (clear-members! (a run r-ancestors))
            (clear-members! (a run r-created))
            (clear-members! (a run r-spawned)))
        (forget-run! rt run))
      (mark! rt (a run r-node)))))

(defn- cancel! [rt run]
  (when (and (has? (a (runtime-field rt :counters) 6) run) (not= :unwinding (a run r-status)))
    (let [node (a run r-node) current? (identical? run (current node))
          predecessor (find! (a node n-runs) (a run r-pred))]
      (retire! rt run)
      (when current?
        (each-copy! [ob (a node n-dependents)] (reject-dependent! rt ob))
        (when (and predecessor (= :stale (a predecessor r-status))) (retire! rt predecessor)))
      (put node n-dirty true))))

(defn- drop-node-events! [rt node]
  (put node n-source-event nil)
  #?(:clj (.removeIf ^java.util.Collection (runtime-field rt :events)
                     (reify java.util.function.Predicate
                       (test [_ event] (identical? node (a event 0)))))
     :cljs (.removeWhere (runtime-field rt :events) (fn [event] (identical? node (a event 0))))))

(defn- signal-dependent? [node]
  ;; Pure one-shot caches have no outgoing reactive registrations. Only idle
  ;; teardown needs this search; publication and hot reentry stay indexed.
  (when (reactive? (current node))
    (loop [todo [node] seen #{}]
      (if-let [node (peek todo)]
        (let [todo (pop todo)]
          (cond
            (contains? seen node) (recur todo seen)
            (or (= :signal (a node n-kind)) (a node n-dirty)) true
            :else
            (recur (into todo (for [run (values (a node n-runs))
                                    ob (items (a run r-obs))
                                    :when (and (reactive-kind? (a ob o-kind)) (a ob o-debtor))]
                                (a ob o-debtor)))
                   (conj seen node))))
        false))))

(defn- reclaim-unwanted! [rt node]
  (when (and (= :spin (a node n-kind)) (a node n-complete))
    (when (signal-dependent? node) (put node n-dirty true))
    (each-copy! [run (values (a node n-runs))] (retire! rt run))
    (owner! rt node nil)
    ;; A live descriptor supplies its body again on invocation. A value-only
    ;; cache must not keep the body's captured descriptors or resources alive.
    (put node n-body nil) (put node n-resume nil))
  (when-not (and (= :spin (a node n-kind)) (a node n-complete)
                 (pos? (count! (a node n-tokens))))
    (each-copy! [run (values (a node n-runs))] (retire! rt run))
    (each-copy! [creator (a node n-created-by)] (uncreate! creator node))
    (drop-node-events! rt node)
    (creator! rt node nil)
    (dissoc! (runtime-field rt :nodes) (a node n-id))
    (put node n-body nil) (put node n-value nil) (put node n-resume nil)
    (clear-members! (a node n-tokens))
    (mark-graph! rt node) (mark! rt node)))

(defn- reclaim! [rt]
  (let [live (runtime-field rt :liveness)]
    ;; Work roots can change at every body boundary; external proofs survive
    ;; stable logical topology even when physical run generations change.
    (clear-live-set! live 2) (clear-live-set! live 3)
    (try
      (loop []
        (when-let [node (pop! (runtime-field rt :work))]
          (put node n-work false)
          (when (and (identical? node (find! (runtime-field rt :nodes) (a node n-id))) (not (wanted? node)))
            (reclaim-unwanted! rt node))
          (recur)))
      (finally
        (reconcile-retention! rt)
        (clear-live-set! live 2) (clear-live-set! live 3)))))

(defn- audit-retention! [rt]
  (each! [node (values (runtime-field rt :nodes))]
         (let [owner (a node n-owner)
               expected (set (filter some?
                                     (concat [(owner-node owner)]
                                             (mapcat (fn [run]
                                                       (when-not (= :unwinding (a run r-status))
                                                         (concat [(owner-node (a run r-owner))]
                                                                 (for [ob (items (a run r-obs)) :when (a ob o-live)] (a ob o-debtor))
                                                                 (filter #(and (open-owner? (a % n-owner)) (owns-live-kind? %))
                                                                         (items (a run r-owned))))))
                                                     (values (a node n-runs))))))
               actual (set (items (a node n-links)))
               external? (boolean (or (and (root-owner? owner) (owns-live-kind? node))
                                      (any! (a node n-dependents) #(and (a % o-live) (nil? (a % o-run))))))]
           (when-not (and (= expected actual) (= external? (boolean (a node n-external-root))))
             (throw (ex-info "Retention graph differs from semantic rows"
                             {:id (a node n-id) :expected (set (map #(a % n-id) expected))
                              :actual (set (map #(a % n-id) actual))
                              :root external? :actual-root (a node n-external-root)})))
           (each! [target (a node n-links)]
                  (when-not (and (identical? target (find! (runtime-field rt :nodes) (a target n-id)))
                                 (has? (a target n-supporters) node))
                    (throw (ex-info "Retention edge has no reverse index" {:id (a node n-id)}))))
           (each! [source (a node n-supporters)]
                  (when-not (and (identical? source (find! (runtime-field rt :nodes) (a source n-id)))
                                 (has? (a source n-links) node))
                    (throw (ex-info "Retention reverse index has no edge" {:id (a node n-id)})))))))

(defn- audit-derived-state! [rt]
  (audit-retention! rt)
  (when-not (zero? (count! empty-members))
    (throw (ex-info "Shared empty membership was mutated" {})))
  #?(:cljs
     (let [heap (runtime-field rt :ready)]
       (dotimes [index (.-length heap)]
         (when (pos? index)
           (let [parent (unsigned-bit-shift-right (dec index) 1)]
             (when (> (a (aget heap parent) n-rank) (a (aget heap index) n-rank))
               (throw (ex-info "Ready heap priority changed while queued" {:index index}))))))))
  (let [nodes (vec (values (runtime-field rt :nodes)))
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

  (each! [node (values (runtime-field rt :nodes))]
         (let [current-active (boolean (active-status? (some-> (current node) (a r-status))))
               any-active (boolean (any! (values (a node n-runs)) #(active-status? (a % r-status))))]
           (when-not (= current-active any-active)
             (throw (ex-info "Active-run projection mismatch" {:entity (a node n-id)})))))
  (each! [run (a (runtime-field rt :counters) 6)]
         (let [actual (count (filter #(reactive-kind? (a % o-kind)) (items (a run r-obs))))]
           (when-not (= actual (or (a run r-reactives) 0))
             (throw (ex-info "Reactive-site count mismatch" {:run (a run r-gen) :expected actual :actual (a run r-reactives)}))))))

(defn- boundary! [rt action]
  (reclaim! rt)
  (prune-ancestry! rt)
  (when-let [audit (runtime-field rt :audit)]
    (audit-derived-state! rt)
    (let [pending (a (runtime-field rt :counters) 9)
          ;; A nil trace keeps structural auditing without retaining worlds.
          recording? (some? @audit)
          action (when recording? (assoc action :fresh-runs (vec (items pending))))]
      #?(:clj (.clear ^java.util.ArrayDeque pending) :cljs (.clear pending))
      (when recording?
        (swap! audit conj [action (snapshot rt) (snapshot-family rt)])))))

(defn- touch! [rt node token]
  (when token (add! (a node n-tokens) token) (add! (a token t-touched) (runtime-field rt :world))))
(defn- check-token! [rt token]
  (when (and token (not (identical? (runtime-field rt :family-id) (a token t-family))))
    (throw (ex-info "Handle belongs to another runtime family" {:error :unknown-handle})))
  (when (and token (has? (a token t-dropped) (runtime-field rt :world)))
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
                  old (find! (runtime-field rt :nodes) id)
                  node (or old (node! rt id :signal (or run (runtime-field rt :owner-root))))]
              (when-not (= :signal (a node n-kind)) (throw (ex-info "Source ID collision" {:id id})))
              (when (or (nil? old) (predecessor-run? (a node n-owner) run))
                (when-not old (put node n-value value))
                (owner! rt node (or run (runtime-field rt :owner-root))) (put node n-order order)
                (when run (creation! run node)))
              (boundary! rt (when (runtime-field rt :audit) (cond-> {:t :t02 :w (runtime-field rt :world) :e id :value value}
                                                              run (assoc :r [(a (a run r-node) n-id) (a run r-gen)] :order order))))
              (->Source id (runtime-field rt :family-id))))))

#?(:clj (defonce ^:private handle-cleaner (java.lang.ref.Cleaner/create))
   :cljs (defonce ^:private handle-cleaner
           (js/FinalizationRegistry.
            (fn [held]
              (when-let [home (.deref (aget held 0))]
                (collect-home-token! home (aget held 1)))))))

(defn- arm-handle! [rt handle token]
  #?(:clj (let [home-ref (java.lang.ref.WeakReference. (runtime-field rt :home))]
            (put token 5 (.register ^java.lang.ref.Cleaner handle-cleaner handle
                                    (reify Runnable
                                      (run [_] (when-let [home (.get home-ref)]
                                                 (collect-home-token! home token)))))))
     :cljs (.register handle-cleaner handle (array (js/WeakRef. (runtime-field rt :home)) token) token))
  handle)

(defn- collect-home-token! [home token]
  (let [target #?(:clj (locking (:gate home)
                        ;; WeakHashMap's reference queue otherwise drains only
                        ;; on the next lookup, retaining stale token metadata.
                         (.size ^java.util.WeakHashMap (:host-tokens home))
                         (first (values (:worlds home))))
                  :cljs (first (values (:worlds home))))]
    (when target (collect-token! target token))))

(defn- collect-token! [rt token]
  (locked rt
          (when (a token t-reachable)
            (put token t-reachable false)
            (each! [world (a token t-touched)]
                   (when-let [target (find! (runtime-field rt :family) world)]
                     (when (find! (:nodes target) (a token t-spin))
                       (push! (runtime-field rt :gc) (doto (slots 2) (put 0 target) (put 1 token))))))
            (boundary! rt (when (runtime-field rt :audit) {:t :t16 :tok (a token t-id)
                                                           :notification-order (mapv #(-> (a % 0) :world)
                                                                                     (items (runtime-field rt :gc)))})))
          (loop []
            (when-let [notification (pop! (runtime-field rt :gc))]
              (let [target (a notification 0) dead (a notification 1)]
                (when-let [node (find! (:nodes target) (a dead t-spin))]
                  (remove! (a node n-tokens) dead) (mark! target node))
                (boundary! target (when (:audit target) {:t :t17 :w (:world target) :e (a dead t-spin) :tok (a dead t-id)})))
              (recur)))))

(defn notify-unreachable!
  "Deterministic exercise of the host-finalization handoff for experiments."
  [rt handle]
  (when-not (identical? (runtime-field rt :family-id) (a (:token handle) t-family))
    (throw (ex-info "Handle belongs to another runtime family" {:error :unknown-handle})))
  #?(:clj (.clean ^java.lang.ref.Cleaner$Cleanable (a (:token handle) 5))
     :cljs (do (.unregister handle-cleaner (:token handle)) (collect-token! rt (:token handle)))))

(defn- new-token [rt id]
  (doto (slots 7)
    (put t-family (runtime-field rt :family-id)) (put t-id (random-uuid))
    (put t-spin id) (put t-reachable true)
    (put t-touched (members)) (put t-dropped (members))))

(defn- construct-token! [rt id token run]
  (check-running! run)
  (when-let [node (find! (runtime-field rt :nodes) id)]
    (when-not (= :spin (a node n-kind))
      (throw (ex-info "Computation ID collision" {:id id}))))
  (when (runtime-field rt :tokens) (add! (runtime-field rt :tokens) token))
  (let [order (if run (put (current-activation) 2 (inc (long (a (current-activation) 2)))) 0)
        node (find! (runtime-field rt :nodes) id)]
    (when (and run (nil? node))
      (let [node (node! rt id :spin run)]
        (creator! rt node run) (kept! rt node (reactive? run)) (put node n-order order)
        (creation! run node)))
    (when-let [node (find! (runtime-field rt :nodes) id)]
      (when (predecessor-run? (a node n-creator) run)
        (adopt! rt node run)
        (owner! rt node run) (creator! rt node run) (kept! rt node (reactive? run))
        (put node n-order order) (creation! run node))
      (touch! rt node token))
    (boundary! rt (when (runtime-field rt :audit) (cond-> {:t :t01 :w (runtime-field rt :world) :e id :tok (a token t-id)}
                                                    run (assoc :r [(a (a run r-node) n-id) (a run r-gen)] :order order))))))

(defn make-spin [requested id body]
  (let [rt (execution-runtime requested) token (new-token rt id)]
    (locked rt (construct-token! rt id token (when (current-activation) (a (current-activation) 1))))
    (arm-handle! rt (->Handle id token body) token)))

(defn- portable-token! [rt target id construction?]
  ;; Only the engine's identity-equality public Spin objects enter this cache.
  ;; Values contain no body, public target or strong reference to the family.
  (locked rt
          (when (and (current-activation) (identical? rt (a (current-activation) 0)))
            (check-running! (a (current-activation) 1)))
          (let [cache (:host-tokens (runtime-field rt :home))]
            (or #?(:clj (.get ^java.util.WeakHashMap cache target) :cljs (.get cache target))
                (let [token (new-token rt id)]
                  ;; First use in another family is not body construction:
                  ;; an existing portable host handle must not acquire a creator.
                  (construct-token! rt id token (when (and construction? (current-activation)
                                                           (identical? rt (a (current-activation) 0)))
                                                  (a (current-activation) 1)))
                  (arm-handle! rt target token)
                  #?(:clj (.put ^java.util.WeakHashMap cache target token) :cljs (.set cache target token))
                  token)))))

(defn- admit-world-switch! [rt]
  ;; An explicit request into another world is a host-root request there.
  ;; Validate the initiating slice under its OWN gate before acquiring the
  ;; destination gate. This is its caller-admission point: later cancellation
  ;; does not retract an already admitted request into an independent world.
  ;; Never read a foreign run's mutable status under the destination gate.
  (when-let [frame (current-activation)]
    (let [caller (a frame 0)]
      (when-not (identical? caller rt)
        (locked caller (check-running! (a frame 1)))))))

(defn register-computation!
  "Record construction of a portable public computation in this family.
  The target must have Object identity equality (the public Spin deftype)."
  [requested target id]
  (try
    (admit-world-switch! requested)
    (portable-token! requested target id true)
    nil
    (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))

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

(defn- ready-add! [rt node]
  #?(:clj (.add ^java.util.PriorityQueue (runtime-field rt :ready) node)
     :cljs (let [heap (runtime-field rt :ready) index (.-length heap) rank (a node n-rank)]
             (.push heap node)
             (loop [index index]
               (if (pos? index)
                 (let [parent (unsigned-bit-shift-right (dec index) 1)
                       above (aget heap parent)]
                   (if (> (a above n-rank) rank)
                     (do (aset heap index above) (recur parent))
                     (aset heap index node)))
                 (aset heap index node))))))

(defn- schedule! [rt node ob]
  (put node n-pending-generation (a (current node) r-gen))
  (let [previous (a node n-resume)]
    (when (or (nil? previous) (and ob (< (long (a ob o-order)) (long (a previous o-order)))))
      (put node n-resume ob)))
  (when-not (a node n-ready)
    (put node n-ready true)
    (ready-add! rt node)))

(defn- run-slots! [rt]
  (or (pop! (a (runtime-field rt :counters) 0))
      (let [run (slots 20)]
        (fields! [field [r-created r-spawned r-obs r-owned r-backlinks r-childruns r-ancestors]]
                 (put run field empty-members))
        run)))

(defn- start! [rt node owner reentry?]
  (when-not reentry? (put node n-resume nil))
  (each-copy! [inherited (values (a node n-runs))]
              (when (= :inherited (a inherited r-status)) (cancel! rt inherited)))
  (let [run (run-slots! rt)
        pred (current node)
        generation (put (runtime-field rt :serial) 1 (inc (long (a (runtime-field rt :serial) 1))))]
    (put node n-generation generation)
    (when (runtime-field rt :audit)
      (assoc! (a (runtime-field rt :counters) 3) (a node n-id) generation)
      (push! (a (runtime-field rt :counters) 9) [(runtime-field rt :world) (a node n-id) generation]))
    (put run r-reactives 0) (put run r-validation-lost nil)
    (when (and pred (not= :unwinding (a pred r-status)))
      (each! [gen (a pred r-ancestors)] (add-run! run r-ancestors gen))
      (add-run! run r-ancestors (a pred r-gen)))
    (put run r-node node) (put run r-gen generation) (put run r-owner owner)
    (put run r-pred (when (and pred (not= :unwinding (a pred r-status))) (a pred r-gen))) (put run r-status :running)
    (put run r-seq (put (runtime-field rt :counters) 1 (inc (max (long (a (runtime-field rt :counters) 1)) (long (a (runtime-field rt :counters) 2))))))
    (assoc! (a node n-runs) generation run)
    (add! (a (runtime-field rt :counters) 6) run)
    (put node n-current run)
    (when-not (root-owner? owner)
      (add-run! owner r-spawned run) (add-run! run r-backlinks owner)
      (add-run! owner r-childruns run) (mark! rt (a owner r-node))
      (when-not (has? (a node n-links) (a owner r-node)) (mark-graph! rt node)))
    (schedule! rt node nil)
    (mark! rt node) run))

(defn- ob! [rt kind debtor run order resolve reject]
  (let [ob (slots 19) id (a (runtime-field rt :serial) 0)]
    (next-number! rt 0)
    (put ob o-id id) (put ob o-kind kind) (put ob o-debtor debtor) (put ob o-run run)
    (when run (put ob o-creditor-generation (a run r-gen)) (put ob o-creditor-node (a run r-node)))
    (put ob o-standing (case kind (:track :await-reactive :callback) true false))
    (put ob o-resolve resolve) (put ob o-reject reject) (put ob o-order order)
    (put ob o-slot (if (= kind :track) :consumed :armed)) (put ob o-live true)
    (when (= :await-once kind) (assoc! (runtime-field rt :deliveries) id ob))
    (when run (add-run! run r-obs ob) (mark! rt (a run r-node))
          (when (and debtor (not (has? (a (a run r-node) n-links) debtor)))
            (mark-graph! rt (a run r-node)))
          (when (reactive-kind? kind) (reactive-delta! run 1)))
    (when debtor
      (add! (a debtor n-dependents) ob) (mark! rt debtor)
      (when (and (nil? run) (not (a debtor n-external-root))) (mark-graph! rt debtor)))
    ob))

(defn- adopt! [rt node caller]
  (let [previous (a node n-owner)]
    (when (predecessor-run? previous caller)
      (when (identical? previous (a node n-creator))
        (creator! rt node caller) (kept! rt node (reactive? caller))
        (creation! caller node))
      (owner! rt node caller)
      (each! [run (values (a node n-runs))]
             (when (identical? previous (a run r-owner))
               (remove! (a previous r-childruns) run) (put run r-owner caller) (add-run! caller r-childruns run))))))

(defn- rank! [run debtor]
  (when debtor
    (let [node (a run r-node) rank (inc (long (a debtor n-rank)))]
      (when (> rank (long (a node n-rank)))
        ;; Both platform queues borrow node priorities. Rank is refined only
        ;; after claiming a slice, never while its node remains queued.
        (when (and (:audit (a node n-runtime)) (a node n-ready))
          (throw (ex-info "Queued priority mutation" {:id (a node n-id)})))
        (put node n-rank rank)))))

(defn- register-track! [rt run order id resolve reject]
  (locked rt
          (check-running! run)
          (let [node (or (find! (runtime-field rt :nodes) id)
                         (throw (ex-info "Foreign or released track is outside this slice" {:id id})))
                ob (ob! rt :track node run order resolve reject)]
            (put ob o-last (a node n-value)) (rank! run node)
            (boundary! rt (when (runtime-field rt :audit) {:t :t05 :w (runtime-field rt :world) :r [(a (a run r-node) n-id) (a run r-gen)]
                                                           :kind :track :order order :debtor [:entity (runtime-field rt :world) id]}))
            (a node n-value))))

(defn- track-id-effect! [id resolve reject resume-resolve resume-reject]
  (let [frame (current-activation) rt (a frame 0) run (a frame 1)
        order (put frame 2 (inc (long (a frame 2))))
        value (register-track! rt run order id resume-resolve resume-reject)]
    (cps/invoke-continuation resolve (iv/->Interval value value nil))))

(defn- check-source! [rt source]
  (when-not (identical? (runtime-field rt :family-id) (:family source))
    (throw (ex-info "Source belongs to another runtime family" {:error :unknown-source}))))

(defn track-effect!
  ([source resolve reject]
   (check-source! (a (current-activation) 0) source)
   (track-id-effect! (:id source) resolve reject resolve reject))
  ([source resolve reject resume-resolve resume-reject]
   (check-source! (a (current-activation) 0) source)
   (track-id-effect! (:id source) resolve reject resume-resolve resume-reject)))

(defn- deliver-value! [resolve reject value failed?]
  (cps/invoke-continuation (if failed? reject resolve) value))
(defn- deliver-cont! [ob value]
  (deliver-value! (a ob o-resolve) (a ob o-reject) value (a ob o-delivery-error)))

(defn- register-await! [rt run order id token body resolve reject]
  (locked rt
          (check-running! run)
          (check-token! rt token)
          (when (and (nil? (find! (runtime-field rt :nodes) id)) (parent-node rt id))
            (throw (ex-info "Foreign await is outside this slice" {:id id})))
          (let [node (or (find! (runtime-field rt :nodes) id) (node! rt id :spin run))]
            (put node n-body body)
            (adopt! rt node run)
            (when-not (a node n-owner) (owner! rt node run))
            (when (and (not (work-status? (some-> (current node) (a r-status))))
                       (or (not (a node n-complete)) (a node n-dirty)))
              (start! rt node run false))
            (let [ob (ob! rt :await-reactive node run order resolve reject)]
              (put run r-status :parked) (touch! rt node token) (rank! run node)
              (let [ready? (and (a node n-complete) (not (a node n-dirty))
                                (not (work-status? (some-> (current node) (a r-status)))))]
                ;; T5+T6 share the gate and run no user code between them. Both
                ;; statuses retain the same standing obligation and ownership;
                ;; one final Rule L closure suffices. Audit mode still exposes
                ;; both model states for the independent transition replay.
                (when (or (not ready?) (runtime-field rt :audit))
                  (boundary! rt (when (runtime-field rt :audit) (cond-> {:t :t05 :w (runtime-field rt :world) :r [(a (a run r-node) n-id) (a run r-gen)]
                                                                         :kind :await-reactive :order order :debtor [:entity (runtime-field rt :world) id]}
                                                                  token (assoc :tok (a token t-id))))))
                (when ready?
                  (put ob o-slot :consumed) (put run r-status :running) (put ob o-value (a node n-value))
                  (put ob o-delivery-error (= :error (a node n-complete)))
                  (boundary! rt (when (runtime-field rt :audit) {:t :t06 :w (runtime-field rt :world) :o [:o (a ob o-id)] :value (diagnostic-value (a node n-value) (a ob o-delivery-error))}))))
              ob))))

(defn- await-id-effect! [id token body resolve reject resume-resolve resume-reject]
  (let [frame (current-activation) rt (a frame 0) run (a frame 1)
        order (put frame 2 (inc (long (a frame 2))))
        ob (register-await! rt run order id token body resume-resolve resume-reject)]
    (when (= :consumed (a ob o-slot)) (deliver-value! resolve reject (a ob o-value) (a ob o-delivery-error)))))

(defn await-effect!
  ([source resolve reject]
   (try
     (await-id-effect! (:id source) (:token source) (:body source) resolve reject resolve reject)
     (finally #?(:clj (java.lang.ref.Reference/reachabilityFence source) :cljs nil))))
  ([source resolve reject resume-resolve resume-reject]
   (try
     (await-id-effect! (:id source) (:token source) (:body source) resolve reject resume-resolve resume-reject)
     (finally #?(:clj (java.lang.ref.Reference/reachabilityFence source) :cljs nil)))))

(defn await-computation-effect!
  "Typed public await handoff; no family-bound Handle wrapper is allocated."
  [target id body resolve reject]
  (try
    (let [rt (a (current-activation) 0)]
      (locked rt
              (check-running! (a (current-activation) 1))
              (when (and (nil? (find! (runtime-field rt :nodes) id)) (parent-node rt id))
                (throw (ex-info "Foreign await is outside this slice" {:id id}))))
      (await-id-effect! id (portable-token! rt target id false) body resolve reject resolve reject))
    (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))

(defn park-effect! [ticket resolve reject]
  (let [rt (a (current-activation) 0) run (a (current-activation) 1)
        order (put (current-activation) 2 (inc (long (a (current-activation) 2))))]
    (locked rt
            (check-running! run)
            (let [ob (ob! rt :await-once nil run order resolve reject)
                  waiters (or (find! (runtime-field rt :tickets) (:id ticket))
                              (assoc! (runtime-field rt :tickets) (:id ticket) (members)))]
              (put ob o-host (:id ticket)) (add! waiters ob)
              (put run r-status :parked)
              (boundary! rt (when (runtime-field rt :audit) {:t :t05 :w (runtime-field rt :world) :r [(a (a run r-node) n-id) (a run r-gen)]
                                                             :kind :await-once :order order :debtor [:host (:id ticket)]}))))))

(defn pending-ticket [requested ticket]
  (let [rt (execution-runtime requested)]
    (locked rt
            (when-let [waiters (find! (runtime-field rt :tickets) (:id ticket))]
              (when-let [ob (first (items waiters))]
                (->Delivery (runtime-field rt :family-id) (runtime-field rt :world) (a ob o-id)))))))

(defn- settle-ticket! [requested delivery value failed?]
  (let [rt (execution-runtime requested)]
    (when-not (and (identical? (runtime-field rt :family-id) (:family delivery)) (= (runtime-field rt :world) (:world delivery)))
      (throw (ex-info "Delivery belongs to a different runtime family or world" {:world (:world delivery)})))
    (locked rt
            (when-let [ob (find! (runtime-field rt :deliveries) (:obligation delivery))]
              (let [run (a ob o-run)]
                (when (and (= :armed (a ob o-slot)) (resumable-status? (a run r-status)))
                  (end-ob! rt ob) (put run r-status :running) (put ob o-value value)
                  (put ob o-delivery-error failed?)
                  (schedule! rt (a run r-node) ob))))
            (boundary! rt (when (runtime-field rt :audit) {:t :t06 :w (runtime-field rt :world)
                                                           :o [:o (:obligation delivery)]
                                                           :value (diagnostic-value value failed?)})))
    (drain! rt)))

(defn resume-ticket! [requested delivery value]
  (settle-ticket! requested delivery value false))

(defn reject-ticket! [requested delivery error]
  (settle-ticket! requested delivery error true))

(defn- deliver-host! [rt delivery value failed?]
  ;; A native callback owns this exact world/registration. In particular, a
  ;; synchronous callback must not redirect through some other active world.
  (locked rt
          (when-let [ob (find! (runtime-field rt :deliveries) (:obligation delivery))]
            (let [run (a ob o-run)]
              (when (and (= :armed (a ob o-slot)) (resumable-status? (a run r-status)))
                (put ob o-slot :consumed)
                (end-ob! rt ob) (put run r-status :running) (put ob o-value value)
                (put ob o-delivery-error failed?)
                (schedule! rt (a run r-node) ob))))
          (boundary! rt (when (runtime-field rt :audit) {:t :t06 :w (runtime-field rt :world)
                                                         :o [:o (:obligation delivery)]
                                                         :value (diagnostic-value value failed?)})))
  (drain! rt))

(defn- host-callback [rt delivery failed?]
  ;; A producer may keep a callback after cancellation/completion. That stale
  ;; capability must not keep the entire world and its application heap alive.
  (let [weak #?(:clj (java.lang.ref.WeakReference. rt) :cljs (js/WeakRef. rt))]
    (fn [value]
      (when-let [target #?(:clj (.get weak) :cljs (.deref weak))]
        (deliver-host! target delivery value failed?)))))

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
                           (assoc! (runtime-field rt :operations) (a ob o-id) operation)
                           (put ob o-host host) (put run r-status :parked)
                           (boundary! rt (when (runtime-field rt :audit) {:t :t05 :w (runtime-field rt :world)
                                                                          :r [(a (a run r-node) n-id) (a run r-gen)]
                                                                          :kind :await-once :order order :debtor [:host host]}))
                           (->Delivery (runtime-field rt :family-id) (runtime-field rt :world) (a ob o-id))))]
    (when (locked rt (= :starting (a operation 0)))
      (let [cancel (try
                     (start (host-callback rt delivery false) (host-callback rt delivery true))
                     (catch #?(:clj Throwable :cljs :default) error
                       (deliver-host! rt delivery error true)
                       nil))]
        (locked rt
                (case (a operation 0)
                  :starting (do (put operation 0 :live) (put operation 1 cancel))
                  :cancelled (when cancel (push! (runtime-field rt :posts) (doto (slots 1) (put 0 cancel))))
                  :settled nil))))
    nil))

(defn- complete!
  ([requested run value] (complete! requested run value false))
  ([requested run value failed?]
   (let [rt (execution-runtime requested)]
     (locked rt
             (let [node (a run r-node)]
               (when (and (identical? run (current node)) (= :running (a run r-status)))
                 (when-not (a node n-complete)
                   (mark-graph! rt node) (mark-graph! rt (owner-node (a node n-owner))))
                 ;; Completion and outcome share one slot: false/true/:error.
                 ;; Cache checks need truthiness; delivery reads the error tag.
                 (put node n-complete (if failed? :error true))
                 (put node n-dirty (boolean (a run r-validation-lost))) (put node n-value value)
                 (put run r-status :completed)
                 (push! (runtime-field rt :events)
                        (doto (slots 4) (put 0 node) (put 1 value) (put 3 failed?)
                              (put 2 (put (runtime-field rt :counters) 2
                                          (inc (max (long (a (runtime-field rt :counters) 1))
                                                    (long (a (runtime-field rt :counters) 2))))))))
                 (each-copy! [previous (values (a node n-runs))]
                             (when (and (not (identical? previous run)) (basis-status? (a previous r-status)))
                               (retire! rt previous)))
                 (mark! rt node))
               (boundary! rt (when (runtime-field rt :audit)
                               {:t :t07 :w (runtime-field rt :world) :r [(a node n-id) (a run r-gen)]
                                :value (diagnostic-value value failed?)})))))))

(defn- reenter! [rt node trigger]
  (let [previous (current node) work? (work-status? (a previous r-status))
        order (a trigger o-order)]
    (each-copy! [old (values (a node n-runs))]
                (when (= :stale (a old r-status)) (retire! rt old)))
    (let [run (start! rt node (a previous r-owner) true)]
      (when (or (a previous r-validation-lost) (a node n-dirty)) (put run r-validation-lost true))
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
        old (a (runtime-field rt :counters) 4)
        buffer (if (< (alength ^objects old) n)
                 (put (runtime-field rt :counters) 4 (slots (max n (* 2 (alength ^objects old))))) old)]
    #?(:clj (.toArray ^java.util.Collection (a node n-dependents) ^objects buffer)
       :cljs (.copyInto (a node n-dependents) buffer))
    n))

(defn- process-event! [rt event]
  (let [node (a event 0) value (a event 1) failed? (a event 3)
        n (subscriber-buffer! rt node)
        dependents (a (runtime-field rt :counters) 4)
        order (when (runtime-field rt :audit) (mapv #(vector :o (a (a dependents %) o-id)) (range n)))]
    (when (identical? event (a node n-source-event)) (put node n-source-event nil))
    (try
      (dotimes [index n]
        (let [ob (a dependents index)]
          (if-let [run (a ob o-run)]
            (if (= :consumed (a ob o-slot))
              (reenter! rt (a ob o-creditor-node) ob)
              (when (and (a ob o-live) (= :parked (a run r-status)))
                (put ob o-slot :consumed) (put ob o-value value) (put ob o-delivery-error failed?) (put run r-status :running)
                (schedule! rt (a ob o-creditor-node) ob)))
            (do (push! (runtime-field rt :hosts)
                       (doto (slots 2) (put 0 (a ob (if failed? o-failure o-success))) (put 1 value)))
                (when (and (a node n-complete) (not (reactive? (current node)))) (end-ob! rt ob))))))
      (boundary! rt (when (runtime-field rt :audit) {:t :t08 :w (runtime-field rt :world) :e (a node n-id) :value (diagnostic-value value failed?)
                                                     :delivery-order order}))
      (finally (dotimes [i n] (put dependents i nil))))))

(defn- poll-ready! [rt]
  #?(:clj (.poll ^java.util.PriorityQueue (runtime-field rt :ready))
     :cljs (let [heap (runtime-field rt :ready) n (.-length heap)]
             (when (pos? n)
               (let [head (aget heap 0) tail (.pop heap) n (dec n)]
                 (when (pos? n)
                   (loop [index 0]
                     (let [left (inc (* 2 index))]
                       (if (< left n)
                         (let [right (inc left)
                               child (if (and (< right n) (< (a (aget heap right) n-rank)
                                                             (a (aget heap left) n-rank))) right left)
                               below (aget heap child)]
                           (if (< (a below n-rank) (a tail n-rank))
                             (do (aset heap index below) (recur child))
                             (aset heap index tail)))
                         (aset heap index tail)))))
                 head)))))

(declare drain!)
(defn- finish-slice! [rt run]
  (locked rt
          (put run r-physical false)
          (put (runtime-field rt :thread) 0 nil)
          (when (= :unwinding (a run r-status)) (forget-run! rt run))
          (boundary! rt (when (runtime-field rt :audit) {:t :t38 :th :engine}))))

(defn- claim-slice! [rt node]
  (locked rt
          (let [run (current node) ob (a node n-resume)]
            (put node n-ready false) (put node n-resume nil)
            (when (and run (= :running (a run r-status)) (= (a run r-gen) (a node n-pending-generation)))
              (when ob (rank! run (a ob o-debtor)))
              (put run r-physical true)
              (put (runtime-field rt :thread) 0 run) (put (runtime-field rt :thread) 1 true) (put (runtime-field rt :thread) 2 (runtime-field rt :world))
              (boundary! rt (when (runtime-field rt :audit) {:t :slice-enter :w (runtime-field rt :world) :r [(a node n-id) (a run r-gen)] :th :engine}))
              (let [frame (a (runtime-field rt :counters) 5) debtor (when ob (a ob o-debtor))]
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
       (fn [error] (complete! rt (a (current-activation) 1) error true))))))

(defn- execute! [rt node]
  (when-let [activation (claim-slice! rt node)]
    (let [run (a activation 1) ob (a activation 3)]
      (try
        (with-activation activation
          (try (invoke-slice! rt activation)
               (catch #?(:clj Throwable :cljs :default) error
                 (try
                   (if ob (cps/invoke-continuation (a ob o-reject) error)
                       (complete! rt run error true))
                   (catch #?(:clj Throwable :cljs :default) rejected
                     (complete! rt run rejected true))))))
        (finally
          (finish-slice! rt run)
          (dotimes [i 8] (put activation i nil)))))))

(defn- next-dispatch! [rt]
  (locked rt
          (if-let [post (pop! (runtime-field rt :posts))]
            post
            (if-let [event (pop! (runtime-field rt :events))]
              (do (process-event! (a (a event 0) n-runtime) event) :event)
              (or (poll-ready! rt) (pop! (runtime-field rt :hosts)))))))

(defn drain! [rt]
  (when (compare-and-set! (runtime-field rt :draining) false true)
    (binding [cps/*in-trampoline* false]
      (let [failure
            (try
              (loop [failure nil]
                (if-let [entry (next-dispatch! rt)]
                  (if (and (not= :event entry) (= 1 (alength ^objects entry)))
                    ;; Logical cancellation is already committed. A failed
                    ;; detach must not strand other cancellation/delivery work.
                    (let [error (try ((a entry 0)) nil
                                     (catch #?(:clj Throwable :cljs :default) error [error]))]
                      (recur (or failure error)))
                    (if (and (not= :event entry) (= 2 (alength ^objects entry)))
                      ;; Host observers own their exceptions. Finish committed
                      ;; deliveries, including reentrant registrations, before
                      ;; reporting the first error to the drain's caller.
                      (let [callback (a entry 0) value (a entry 1)
                            error (try
                                    (callback value)
                                    nil
                                    (catch #?(:clj Throwable :cljs :default) error [error]))]
                        (recur (or failure error)))
                      (do
                        (when-not (= :event entry) (execute! (a entry n-runtime) entry))
                        (recur failure))))
                  failure))
              (finally (reset! (runtime-field rt :draining) false)))]
        (let [later-failure
              (try
                (when (locked rt (or (queued? (runtime-field rt :posts)) (queued? (runtime-field rt :events)) (queued? (runtime-field rt :hosts))
                                     #?(:clj (not (.isEmpty ^java.util.PriorityQueue (runtime-field rt :ready)))
                                        :cljs (pos? (.-length (runtime-field rt :ready))))))
                  (drain! rt))
                nil
                (catch #?(:clj Throwable :cljs :default) error [error]))]
          ;; A tagged error also preserves JavaScript's `throw null/false`.
          (when-let [error (or failure later-failure)] (throw (first error))))))))

(defn- observe-token! [rt id token body success failure]
  (let [ob (locked rt
                   (when (and (current-activation) (identical? rt (a (current-activation) 0)))
                     (check-running! (a (current-activation) 1)))
                   (check-token! rt token)
                   (when (and (nil? (find! (runtime-field rt :nodes) id)) (parent-node rt id))
                     (throw (ex-info "Foreign invocation is outside this slice" {:id id})))
                   (let [node (or (find! (runtime-field rt :nodes) id) (node! rt id :spin (runtime-field rt :owner-root)))
                         cached? (and (a node n-complete) (not (a node n-dirty)) (not (work-status? (some-> (current node) (a r-status)))))]
                     (put node n-body body)
                     (when-not (a node n-owner) (owner! rt node (runtime-field rt :owner-root)))
                     (touch! rt node token)
                     (when-not (or cached? (work-status? (some-> (current node) (a r-status)))) (start! rt node (runtime-field rt :owner-root) false))
                     (let [ob (ob! rt :callback node nil 0 nil nil)]
                       (put ob o-success success) (put ob o-failure failure)
                       (when cached?
                         (push! (runtime-field rt :hosts) (doto (slots 2) (put 0 (a ob (if (= :error (a node n-complete)) o-failure o-success)))
                                                                (put 1 (a node n-value))))
                         (when-not (reactive? (current node)) (end-ob! rt ob)))
                       (boundary! rt (when (runtime-field rt :audit) {:t :t04 :w (runtime-field rt :world) :e id :tok (a token t-id) :mode :callback}))
                       ob)))]
    (drain! rt)
    (fn []
      (locked rt
              (end-ob! rt ob)
              (boundary! rt (when (runtime-field rt :audit) {:t :unsubscribe :w (runtime-field rt :world) :o [:o (a ob o-id)]})))
      (drain! rt))))

(defn observe! [requested handle success failure]
  (try
    (observe-token! (execution-runtime requested) (:id handle) (:token handle) (:body handle) success failure)
    (finally #?(:clj (java.lang.ref.Reference/reachabilityFence handle) :cljs nil))))

(defn invoke-computation!
  "Typed public invocation; token identity is local to the runtime family."
  [requested target id body success failure]
  (try
    (admit-world-switch! requested)
    (let [rt requested]
      (locked rt
              (when (and (nil? (find! (runtime-field rt :nodes) id)) (parent-node rt id))
                (throw (ex-info "Foreign invocation is outside this slice" {:id id}))))
      (observe-token! rt id (portable-token! rt target id false) body success failure))
    (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))

(defn- source-node! [rt source unwinding?]
  (let [node (find! (runtime-field rt :nodes) (:id source))]
    (when-not (or (and unwinding? (nil? node))
                  (and node (= :signal (a node n-kind)) (or (a node n-owner) unwinding?)))
      (throw (ex-info "Released source" {:id (:id source)})))
    node))

(def ^:private engine-state-keys
  #{:nodes :spin-tracking :subscriptions :track-subscriptions :await-conts
    :entities :runs :obligations :queue :lineage :root :status :admission :seal-seq
    :seq :serial :clock :handles :threads :gc :global :scopes :pins
    :fdeps :releasing :cuts :caps :registry})

(defn- engine-path? [path]
  (let [key (first path)]
    (or (contains? engine-state-keys key)
        (and (keyword? key) (#{"engine" "lifetime"} (namespace key))))))

(defn- application-write! [path]
  (when (or (empty? path) (engine-path? path))
    (throw (ex-info "Engine state requires a typed operation" {:error :engine-state-read-only :path path}))))

(defn- application-roots [rt]
  ;; The family gate is held by the caller. Keep immutable roots, never a
  ;; mutable row alias, and do not retain these borrowed views after the call.
  (loop [world rt result []]
    (if world
      (recur (runtime-field world :parent)
             (conj result [world @(runtime-field world :extension-state)]))
      result)))

(defn- application-values [roots]
  (reduce (fn [parent [_ {:keys [values shadowed]}]]
            (reduce (fn [result path]
                      (if (= 1 (count path))
                        (assoc-in result path (get-in values path))
                        (let [[group cell] path parent (get result group)]
                          (assoc result group (assoc (if (map? parent) parent {}) cell (get-in values path))))))
                    parent shadowed))
          {} (reverse roots)))

(defn- application-group-base [roots group]
  ;; Only the shape is needed for a map group; return a vector/scalar base
  ;; directly so nested vector edits can preserve the complete vector value.
  (some (fn [[_ {:keys [values shadowed map-groups]}]]
          (cond (contains? shadowed [group]) [true (get values group)]
                (contains? map-groups group) [true {}])) roots))

(defn- application-value [roots path]
  (if (< (count path) 2)
    (get-in (application-values roots) path)
    (let [top (first path) group [top] cell (subvec path 0 2)]
      (loop [roots (seq roots)]
        (when-let [[_ {:keys [values shadowed map-groups]}] (first roots)]
          (cond
            (or (contains? shadowed group) (contains? shadowed cell)) (get-in values path)
            (and (contains? map-groups top)
                 (not (map? (second (application-group-base (next roots) top))))) nil
            :else (recur (next roots))))))))

(defn- application-candidate [roots path value]
  (let [state (second (first roots))
        group [(first path)] cell (if (= 1 (count path)) group (subvec path 0 2))
        base (second (application-group-base roots (first path)))]
    (if (and (> (count path) 1) (some? base) (not (map? base)))
      (application-candidate roots group (assoc-in base (subvec path 1) value))
      (let [values (if (or (= 1 (count path)) (contains? (:shadowed state) group)
                           (contains? (:shadowed state) cell))
                     (:values state)
                     (assoc-in (:values state) cell (application-value roots cell)))
            shadowed (:shadowed state)
            shadowed (if (= 1 (count path))
                       (set (remove #(= (first %) (first path)) shadowed)) shadowed)
            updated-values (assoc-in values path value)
            updated-shadowed (if (contains? shadowed group) shadowed (conj shadowed cell))
            map-groups (if (= 1 (count path)) (disj (:map-groups state) (first path))
                           (if (contains? shadowed group) (:map-groups state)
                               (conj (:map-groups state) (first path))))]
        (if (and (identical? updated-values (:values state)) (= updated-shadowed (:shadowed state))
                 (= map-groups (:map-groups state)))
          state
          {:values updated-values :shadowed updated-shadowed :map-groups map-groups})))))

(defn- application-roots-current? [roots]
  (every? (fn [[world before]] (identical? before @(runtime-field world :extension-state))) roots))

(defn read-application-state
  "PState application cells and explicit immutable engine diagnostics. Reads
   of a cell borrow no mutable engine row. Engine paths cannot be mutated."
  [requested path]
  (let [rt requested]
    (cond
      (empty? path) (let [[graph roots] (locked rt [(snapshot rt) (application-roots rt)])]
                      (merge graph (application-values roots)))
      (engine-path? path) (get-in (snapshot rt) path)
      :else (application-value (locked rt (application-roots rt)) path))))

(defn- check-application-caller! [rt]
  ;; Called under the target gate. Related worlds share that gate; unrelated
  ;; worlds use the explicit admission check before acquiring the target.
  (when-let [frame (current-activation)]
    (when (identical? (runtime-field rt :gate) (runtime-field (a frame 0) :gate))
      (check-running! (a frame 1)))))

(defn swap-application-state!
  "User transformations run outside the family gate. Commit retries if any
   application cell changed, and is serialized with fork/capture boundaries."
  [requested path f args]
  (application-write! path)
  (let [rt requested state (runtime-field rt :extension-state)]
    (admit-world-switch! rt)
    (loop []
      (let [roots (locked rt (check-application-caller! rt) (application-roots rt)) before (second (first roots))
            value (application-value roots path)
            after (if (seq args) (apply f value args) (f value))
            candidate (application-candidate roots path after)
            _ (admit-world-switch! rt)
            committed? (locked rt
                               (check-application-caller! rt)
                               (when (application-roots-current? roots)
                                 (compare-and-set! state before candidate)))]
        (if committed? after (recur))))))

(defn cas-application-state! [requested path old-value new-value]
  (application-write! path)
  (let [rt requested state (runtime-field rt :extension-state)]
    (admit-world-switch! rt)
    (loop []
      (let [roots (locked rt (check-application-caller! rt) (application-roots rt)) before (second (first roots))]
        ;; Equality and key hashing may call user code, including a reentrant
        ;; update. Construct the candidate outside the gate, then compare the
        ;; complete immutable root by identity so those updates are preserved.
        (if (= old-value (application-value roots path))
          (let [candidate (application-candidate roots path new-value)
                _ (admit-world-switch! rt)]
            (if (locked rt (check-application-caller! rt)
                        (when (application-roots-current? roots)
                          (compare-and-set! state before candidate)))
              true (recur)))
          false)))))

(defn read-signal [requested source]
  (let [rt (execution-runtime requested)]
    (check-source! rt source)
    (locked rt (a (source-node! rt source false) n-value))))

(defn- write-source! [rt node source value]
  (when node
    (put node n-value value)
    (let [old (a node n-source-event)
          event (or old (slots 4))]
      ;; These are invalidations of state, rather than a lossless change feed.
      ;; Moving the newest envelope to the tail preserves retained FIFO order.
      (when old
        #?(:clj (.remove ^java.util.ArrayDeque (runtime-field rt :events) old)
           :cljs (.remove (runtime-field rt :events) old)))
      (put node n-source-event event)
      (put event 0 node) (put event 1 value)
      (put event 2 (put (runtime-field rt :counters) 2 (inc (max (long (a (runtime-field rt :counters) 1))
                                                                 (long (a (runtime-field rt :counters) 2))))))
      (push! (runtime-field rt :events) event)))
  (boundary! rt (when (runtime-field rt :audit) (cond-> {:t :signal-write :w (runtime-field rt :world) :e (:id source) :value value}
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
            (let [node (find! (runtime-field rt :nodes) (:id handle)) run (when node (current node))
                  id (when run [(a node n-id) (a run r-gen)])]
              (when run (cancel! rt run))
              (boundary! rt (when (runtime-field rt :audit) {:t :t11 :w (runtime-field rt :world) :r id}))))
    (drain! rt)))

(defn release-idle! [requested]
  (let [rt (execution-runtime requested)]
    (locked rt
            (doseq [node (vec (values (runtime-field rt :nodes)))
                    :when (and (= :spin (a node n-kind)) (a node n-complete) (not (wanted? node)))]
              (doseq [token (items (a node n-tokens))] (add! (a token t-dropped) (runtime-field rt :world)))
              (clear-members! (a node n-tokens))
              (mark! rt node))
            (boundary! rt (when (runtime-field rt :audit) {:t :t18 :w (runtime-field rt :world)})))))

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
  (let [worlds (values (runtime-field rt :family))]
    {:registry (set (map :world worlds)) :known-worlds (set (map :world worlds))
     :lineages (into {} (map (juxt :world :lineage) worlds))
     :caps (map-value (a (runtime-field rt :counters) 7))
     :generation-clock (into {} (for [world worlds :let [clock (a (:counters world) 3)] :when clock [id n] (map-value clock)]
                                  [[(:world world) id] n]))}))

(defn- all-obligations [rt]
  ;; Internal graph links already own reactive registrations. Only ticket
  ;; deliveries need lookup by a host-visible registration number.
  (concat (mapcat #(items (a % r-obs)) (items (a (runtime-field rt :counters) 6)))
          (for [node (values (runtime-field rt :nodes)) ob (items (a node n-dependents))
                :when (nil? (a ob o-run))] ob)))

(defn snapshot [rt]
  (locked rt
          {:global (global-view rt) :lineage (runtime-field rt :lineage) :root (runtime-field rt :root) :status :live :admission :open :seal-seq nil
           :scopes {(runtime-field rt :root) {:kind (if (runtime-field rt :parent) :fork :world-root) :parent nil :status :open}}
           :pins #{} :fdeps #{} :releasing #{}
           :entities (into {} (for [node (values (runtime-field rt :nodes))]
                                [(a node n-id)
                                 (cond-> {:kind (a node n-kind) :origin (or (a node n-origin) :created) :owner (owner-id (a node n-owner))
                                          :creator (run-id (a node n-creator)) :completed? (boolean (a node n-complete))
                                          :kept? (boolean (a node n-kept)) :result (diagnostic-value (a node n-value) (= :error (a node n-complete)))
                                          :tokens (set (map #(a % t-id) (items (a node n-tokens)))) :key nil :order (a node n-order)}
                                   (some? (a node n-dirty)) (assoc :dirty? (a node n-dirty))
                                   (a node n-source-world) (assoc :source-world (a node n-source-world)))]))
           :runs (into {} (for [run (items (a (runtime-field rt :counters) 6)) :let [node (a run r-node)]]
                            [(run-id run) (cond-> {:spin (a node n-id) :owner (owner-id (a run r-owner))
                                                   :pred (when-let [gen (a run r-pred)] [(a node n-id) gen])
                                                   :ancestors (set (map #(vector (a node n-id) %) (items (a run r-ancestors))))
                                                   :status (a run r-status) :seq (a run r-seq)
                                                   :creations (set (map #(a % n-id) (items (a run r-created))))
                                                   :spawned (set (map run-id (items (a run r-spawned))))}
                                            (a run r-validation-lost) (assoc :validation-lost? true)
                                            (= :unwinding (a run r-status)) (assoc :retired? true :anchor (a run r-anchor))
                                            (a run r-origin) (assoc :origin (a run r-origin) :source-world (a run r-source-world)))]))
           :obligations (into {} (for [ob (all-obligations rt)]
                                   [[:o (a ob o-id)]
                                    (cond-> {:kind (a ob o-kind) :debtor (if-let [debtor (a ob o-debtor)]
                                                                           [:entity (:world (a debtor n-runtime)) (a debtor n-id)]
                                                                           [:host (a ob o-host)])
                                             :creditor (if-let [run (a ob o-run)] [:run (runtime-field rt :world) (run-id run)] [:host :caller])
                                             :standing? (a ob o-standing) :cont (when (a ob o-run) [:continuation [:o (a ob o-id)]])
                                             :token nil :order (a ob o-order) :slot (a ob o-slot)}
                                      (a ob o-run) (assoc :origin (or (a ob o-origin) :created))
                                      (a ob o-source-world) (assoc :source-world (a ob o-source-world))
                                      (nil? (a ob o-run)) (assoc :filter {:mode :local :origin (runtime-field rt :world)}))]))
           :queue (mapv (fn [event] (cond-> {:completion (a (a event 0) n-id) :debtor-world (runtime-field rt :world) :value (diagnostic-value (a event 1) (a event 3)) :seq (a event 2)}
                                      (= :signal (a (a event 0) n-kind)) (assoc :source-change? true)))
                        (filter #(identical? rt (a (a % 0) n-runtime))
                                (items (runtime-field rt :events))))
           :seq (a (runtime-field rt :counters) 1)
           :serial (a (runtime-field rt :serial) 0) :clock (a (runtime-field rt :counters) 2)
           :threads (let [run (a (runtime-field rt :thread) 0)]
                      (cond-> {:host {:world (a (runtime-field rt :thread) 3) :scope nil :run nil :read-permits #{} :excl-permits []}}
                        (a (runtime-field rt :thread) 1)
                        (assoc :engine (cond-> {:world (a (runtime-field rt :thread) 2) :scope (run-id run) :run (run-id run) :executing? (boolean run)}
                                         run (assoc :obligation-world (a (runtime-field rt :thread) 2))
                                         (= :unwinding (some-> run (a r-status))) (assoc :retired? true)))))
           :gc (mapv (fn [notification]
                       (let [target (a notification 0) token (a notification 1)]
                         {:t :t17 :w (:world target) :e (a token t-spin) :tok (a token t-id)}))
                     (items (runtime-field rt :gc)))
           :handles (when (runtime-field rt :tokens)
                      (into {} (for [token (items (runtime-field rt :tokens))]
                                 [(a token t-id) {:spin (a token t-spin) :reachable? (a token t-reachable)
                                                  :touched (set (items (a token t-touched))) :dropped (set (items (a token t-dropped)))}])))}))

(defn fork-parked!
  "Prototype T19 for quiescent host-ticket bundles. Copies the ownership
  closure into independent mutable slots. Entity-debtor bundles and explicit
  scopes are refused until their cross-world retention path is implemented."
  [rt world]
  (locked rt
          (when (find! (runtime-field rt :family) world)
            (throw (ex-info "World ID already used" {:world world})))
          (when (or (a (runtime-field rt :thread) 0) (queued? (runtime-field rt :events)))
            (throw (ex-info "Fork requires a parked boundary" {:world (runtime-field rt :world)})))
          (let [copies (vec (filter #(= :parked (a % r-status)) (items (a (runtime-field rt :counters) 6))))
                run-map (dict)
                selected (members)]
            (each! [run (a (runtime-field rt :counters) 6)]
                   (when (fork-busy-status? (a run r-status))
                     (throw (ex-info "Fork requires a parked boundary" {:world (runtime-field rt :world)}))))
            (doseq [run copies]
              (each! [ob (a run r-obs)]
                     (when (find! (runtime-field rt :operations) (a ob o-id))
                       (throw (ex-info "Native operations require fork recovery" {:world (runtime-field rt :world)})))
                     (when (or (a ob o-debtor) (not= :await-once (a ob o-kind)))
                       (throw (ex-info "Entity-debtor bundles are outside this slice" {:world (runtime-field rt :world)}))))
              (add! selected (a run r-node)))
            (each! [node (values (runtime-field rt :nodes))]
                   (when (some #(or (identical? % (a node n-owner)) (identical? % (a node n-creator))) copies)
                     (add! selected node)))
            (let [child (assoc (runtime {:audit? (boolean (runtime-field rt :audit)) :world-id world})
                               :gate (runtime-field rt :gate) :family (runtime-field rt :family) :family-id (runtime-field rt :family-id) :parent rt
                               :events (runtime-field rt :events) :hosts (runtime-field rt :hosts) :posts (runtime-field rt :posts) :ready (runtime-field rt :ready) :draining (runtime-field rt :draining)
                               :serial (runtime-field rt :serial) :thread (runtime-field rt :thread) :gc (runtime-field rt :gc) :home (runtime-field rt :home)
                               :audit (runtime-field rt :audit) :tokens (runtime-field rt :tokens)
                               :lineage {:parent (runtime-field rt :world) :root (get-in rt [:lineage :root])
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
                       (put copy n-origin :inherited) (put copy n-source-world (runtime-field rt :world))
                       (each! [token (a node n-tokens)] (add! (a copy n-tokens) token))))
              (doseq [run copies]
                (let [copy (slots 20) node (find! node-map (a run r-node))]
                  (assoc! run-map run copy)
                  (put copy r-node node) (put copy r-gen (a run r-gen))
                  (put copy r-owner (:owner-root child)) (put copy r-pred (a run r-pred))
                  (put copy r-status :inherited) (put copy r-seq (a run r-seq)) (put copy r-reactives 0)
                  (put copy r-validation-lost (a run r-validation-lost))
                  (put copy r-origin :inherited) (put copy r-source-world (runtime-field rt :world))
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
                           (put clone o-origin :inherited) (put clone o-source-world (runtime-field rt :world))
                           (add-run! copy r-obs clone)
                           (when (reactive-kind? (a clone o-kind)) (reactive-delta! copy 1))
                           (when (= :await-once (a clone o-kind)) (assoc! (:deliveries child) (a clone o-id) clone))
                           (let [waiters (or (find! (:tickets child) (a clone o-host))
                                             (assoc! (:tickets child) (a clone o-host) (members)))]
                             (add! waiters clone))))))
              (reclaim! child)
              (prune-ancestry! child)
              (put (:counters child) 1 (a (runtime-field rt :counters) 1))
              (put (:counters child) 7 (a (runtime-field rt :counters) 7))
              (assoc! (a (runtime-field rt :counters) 7) [:cap world]
                      {:world world :scope #{} :holder (runtime-field rt :root) :disposition :open :published? true
                       :op nil :pred nil :successors [] :durable? false :bases {}})
              (assoc! (runtime-field rt :family) world child)
              (node! rt [:fork world] :fork (runtime-field rt :owner-root))
              (each! [node (values (:nodes child))]
                     (each! [token (a node n-tokens)] (add! (a token t-touched) world)))
              (boundary! rt (when (runtime-field rt :audit) {:t :t19 :w (runtime-field rt :world) :v world :k [:cap world]
                                                             :scope (runtime-field rt :root) :systems #{}}))
              child))))

(defn snapshot-family [rt]
  (locked rt
          (into {} (for [world (values (runtime-field rt :family))] [(:world world) (snapshot world)]))))

(defn storage-stats [rt]
  (locked rt
          (let [runs (a (runtime-field rt :counters) 6)
                pool (items (a (runtime-field rt :counters) 0))]
            {:live-runs (count! runs)
             :idle-body-references
             (count (for [node (values (runtime-field rt :nodes))
                          :when (and (= :spin (a node n-kind)) (a node n-complete)
                                     (nil? (current node)) (a node n-body))] node))
             :liveness-scratch-references
             (let [live (runtime-field rt :liveness)]
               (+ (count! (a live 2)) (count! (a live 3))
                  #?(:clj (.size ^java.util.ArrayDeque (a live 4))
                     :cljs (alength (.toArray (a live 4))))
                  #?(:clj (.size ^java.util.Map (a live 5))
                     :cljs (.-size (a live 5)))))
             :stale-liveness-references
             (let [indexed? #(identical? % (find! (runtime-field rt :nodes) (a % n-id)))]
               (+ (count (remove indexed? (items (a (runtime-field rt :liveness) 1))))
                  (reduce + 0 (for [node (values (runtime-field rt :nodes))]
                                (count (remove indexed? (concat (items (a node n-links))
                                                                (items (a node n-link-buffer))
                                                                (items (a node n-supporters)))))))))
             :ancestry-references (reduce + 0 (map #(count! (a % r-ancestors)) (items runs)))
             :pooled-runs (count pool)
             :pooled-references
             (reduce + 0 (for [run pool]
                           (+ (count (filter some? (map #(a run %) [r-node r-owner r-pred r-anchor])))
                              (reduce + 0 (map #(count! (a run %))
                                               [r-created r-spawned r-obs r-owned r-backlinks r-childruns r-ancestors])))))
             :orphan-creation-links
             (count (for [node (values (runtime-field rt :nodes)) creator (items (a node n-created-by))
                          :when (not (has? runs creator))] creator))
             :scratch-references (count (filter some? (seq (a (runtime-field rt :counters) 4))))
             :stale-queue-references
             #?(:clj 0
                :cljs (reduce + 0 (map #(.staleReferences %)
                                       (cond-> [(runtime-field rt :events) (runtime-field rt :hosts) (runtime-field rt :work) (runtime-field rt :posts) (runtime-field rt :gc)
                                                (a (runtime-field rt :counters) 0)]
                                         (runtime-field rt :audit) (conj (a (runtime-field rt :counters) 9))))))})))
