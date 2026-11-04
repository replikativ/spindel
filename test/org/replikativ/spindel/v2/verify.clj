(ns org.replikativ.spindel.v2.verify
  "Reference Rule R (§3): `live(W)` by a full trace from the §3.1 roots over
   the §3.2 edges, compared after every commit with what the engine's
   retention counts kept."
  (:require [org.replikativ.spindel.v2.rows :as rw]))

(defn- t [^objects row] (long (aget row rw/TYPE)))
(defn- f [^objects row i] (aget row (int i)))

(defn- rows [w] (vals (f w rw/W-REG)))

(defn- current-or-predecessor
  "§3.2 (Z#1): C.run if current, or if C needs a run and C.run is not done."
  [c]
  (when-let [r (f c rw/C-RUN)]
    (let [current? (== (long (f r rw/R-EPOCH)) (long (f c rw/C-EPOCH)))
          done? (== rw/ACT-DONE (long (f r rw/R-ACT)))]
      (when (or current? (not done?)) r))))

(defn- successors [row]
  (condp == (t row)
    rw/T-COMP (when-not (f row rw/C-IDLE)
                (concat (some-> (current-or-predecessor row) list)
                        (f row rw/C-INS)
                        (f row rw/C-BASIS)
                        (f row rw/C-ADOPT)
                        (map #(f % rw/E-DEBTOR) (f row rw/C-ADOPT-BASE))))
    rw/T-RUN (when-not (== rw/ACT-DONE (long (f row rw/R-ACT)))
               (concat [(f row rw/R-OF)]
                       (some-> (f row rw/R-ACTV) list)
                       (some-> (f row rw/R-SROW) list)))
    rw/T-ACT (let [x (f (f row rw/A-RUN) rw/R-OF)]
               (concat (when (== rw/T-COMP (t x))
                         (filter #(identical? row (f % rw/E-ACT)) (f x rw/C-INS)))
                       (filter #(and % (== rw/EK-WAIT (long (f % rw/E-KIND)))) (f row rw/A-MEMBERS))))
    rw/T-SCOPE (concat (some-> (f row rw/S-PARENT) list)
                       (keep #(f % rw/K-RUN) (f row rw/S-TASKS)))
    rw/T-TASK (some-> (f row rw/K-RUN) list)
    rw/T-EDGE [(f row rw/E-DEBTOR)]
    nil))

(defn live
  "The least set containing the roots and closed under `successors`."
  [w]
  (let [reg (rows w)
        roots (concat [(f w rw/W-ROOT)]
                      (keys (f w rw/W-PINS))
                      ;; observe edges, and host awaits (pending host promises)
                      (filter #(and (== rw/T-EDGE (t %))
                                    (let [k (long (f % rw/E-KIND))]
                                      (or (== k rw/EK-OBSERVE)
                                          (and (== k rw/EK-WAIT) (fn? (f % rw/E-CRED))))))
                              reg))
        seen (java.util.IdentityHashMap.)]
    (loop [todo (vec roots)]
      (when-let [x (peek todo)]
        (let [todo (pop todo)]
          (if (.containsKey seen x)
            (recur todo)
            (do (.put seen x true)
                (recur (into todo (remove nil?) (successors x))))))))
    seen))

(defn- admitted?
  "§3.4: rows kept without engine reason."
  [row]
  (condp == (t row)
    rw/T-COMP (and (f row rw/C-IDLE) (pos? (long (f row rw/HANDLES))))
    rw/T-SOURCE (pos? (long (f row rw/HANDLES)))
    rw/T-TASK (and (f row rw/K-DONE) (pos? (long (f row rw/HANDLES))))
    ;; a closed scope stays until its subtree is empty (Z#18)
    rw/T-SCOPE (not (f row rw/S-OPEN))
    ;; a run whose slice is still on the host stack retires at slice exit (T13)
    rw/T-RUN (boolean (f row rw/R-SLICE))
    false))

(defn- cleanup-rows
  "§3.2 cleanup table: a done run that is not retired keeps its run scope and
   that scope's subtree as storage."
  [w]
  (let [seen (java.util.IdentityHashMap.)]
    (loop [todo (vec (keep #(when (and (== rw/T-RUN (t %)) (== rw/ACT-DONE (long (f % rw/R-ACT))))
                              (f % rw/R-SROW))
                           (rows w)))]
      (when-let [x (peek todo)]
        (let [todo (pop todo)]
          (if (.containsKey seen x)
            (recur todo)
            (do (.put seen x true)
                (recur (into todo (when (== rw/T-SCOPE (t x)) (f x rw/S-CHILDREN)))))))))
    seen))

(defn violations
  "Rows the engine keeps that the reference does not, and non-idle
   computations outside live (§3.3 normalization)."
  [w]
  (let [lv (live w)
        _ (.putAll ^java.util.IdentityHashMap lv ^java.util.Map (cleanup-rows w))]
    (vec (for [row (rows w)
               :when (not (.containsKey ^java.util.IdentityHashMap lv row))
               :when (not (admitted? row))]
           {:type (t row) :id (f row rw/ID)
            :idle (when (== rw/T-COMP (t row)) (f row rw/C-IDLE))}))))

(defn checking-hook
  "A world hook that records Rule R divergences per commit into `acc`."
  [acc]
  (fn [w item]
    (let [v (violations w)]
      (when (seq v) (swap! acc conj {:item item :violations v})))))

;; ---------------------------------------------------------------------------
;; Projection of the engine state to the §2 tables (oracle input, §11.4)

(deftype IdentityKey [x]
  Object
  (equals [_ o] (and (instance? IdentityKey o) (identical? x (.-x ^IdentityKey o))))
  (hashCode [_] (System/identityHashCode x)))

(defn- by-identity? [x]
  (or (fn? x) (.isArray (class x))
      (not (or (number? x) (string? x) (keyword? x) (symbol? x) (boolean? x) (char? x) (coll? x)))))

(defn- intern! [w x]
  (if (nil? x)
    0
    (let [^java.util.Map m (f w rw/W-INTERN)
          k (if (by-identity? x) (->IdentityKey x) x)]
      (or (.get m k)
          (let [n (inc (.size m))] (.put m k n) n)))))

(defn- id [row] (when row (f row rw/ID)))

(defn- result [w row]
  (when (some? (f row rw/C-DONE-EPOCH))
    [(if (f row rw/C-ERR) :err :ok) (intern! w (f row rw/C-RESULT))]))

(defn- owner-id [x] (when x (if (instance? (Class/forName "[Ljava.lang.Object;") x) (id x) x)))

(defn projection
  "{table {id row-map}} with §2 field names; nil is none."
  [w]
  (let [reg (rows w)
        by (group-by t reg)
        tbl (fn [type f] (into (sorted-map) (map (fn [r] [(id r) (f r)])) (get by type)))]
    {:scopes (merge (tbl rw/T-SCOPE (fn [s] {:parent (id (f s rw/S-PARENT)) :kind (f s rw/S-KIND) :open (f s rw/S-OPEN)}))
                    ;; run scopes are materialized lazily; their ids come from the run
                    (into {} (map (fn [r] [(f r rw/R-SCOPE) {:parent nil :kind :run :open true}]))
                          (get by rw/T-RUN)))
     :comps (tbl rw/T-COMP
                 (fn [c] {:owner (owner-id (f c rw/OWNER)) :inputs (intern! w (f c rw/C-INPUTS))
                          :body (intern! w (f c rw/C-BODY)) :run (id (f c rw/C-RUN))
                          :epoch (f c rw/C-EPOCH) :done-epoch (f c rw/C-DONE-EPOCH)
                          :pending (f c rw/C-PENDING) :rank (f c rw/C-RANK) :version (f c rw/VERSION)
                          :result (result w c) :idle (f c rw/C-IDLE)
                          :validity (let [v (f c rw/C-VALIDITY)]
                                      (if (sequential? v) (mapv (fn [[d ver]] [(id d) ver]) v) v))
                          :basis (mapv (fn [x] [(id x) (f x rw/AT)]) (f c rw/C-BASIS))
                          :adoption (when (or (f c rw/C-ADOPT) (f c rw/C-ADOPT-BASE))
                                      {:basis (mapv id (f c rw/C-ADOPT))
                                       :baselines (mapv (fn [e] [(f e rw/E-AT) (id (f e rw/E-DEBTOR))
                                                                 (intern! w (f e rw/E-BASE))])
                                                        (f c rw/C-ADOPT-BASE))})
                          :handles (f c rw/HANDLES)}))
     :runs (tbl rw/T-RUN
                (fn [r] {:of (id (f r rw/R-OF)) :stamp (id r) :epoch (f r rw/R-EPOCH)
                         :scope (f r rw/R-SCOPE)
                         :act ([:active :parked :done] (f r rw/R-ACT))
                         :mode ([:normal :unwinding] (f r rw/R-MODE))
                         :slice (f r rw/R-SLICE) :effect-index (f r rw/R-EIDX)
                         :finalizers [] :resources []}))
     :sources (tbl rw/T-SOURCE
                   (fn [x] {:owner (owner-id (f x rw/OWNER))
                            :kind ([:signal :cell :deferred :mailbox :semaphore] (f x rw/X-KIND))
                            :state (intern! w (f x rw/X-VALUE)) :version (f x rw/VERSION)
                            :open (f x rw/X-OPEN) :handles (f x rw/HANDLES)}))
     :edges (tbl rw/T-EDGE
                 (fn [e] (let [k (long (f e rw/E-KIND))
                               cred (f e rw/E-CRED)]
                           {:kind ([:dep :wait :observe :savepoint] k)
                            :creditor (if (fn? cred) 0 (id cred))
                            :debtor (id (f e rw/E-DEBTOR))
                            :cont (if-let [kk (f e rw/E-CONT)] (intern! w kk) :restart)
                            :at (f e rw/E-AT)
                            :phase (if (f e rw/E-ARMED) :armed :fired)
                            :marked (f e rw/E-MARKED)
                            :seen (f e rw/E-SEEN)
                            :baseline (when (== k rw/EK-DEP)
                                        (when (== rw/T-SOURCE (t (f e rw/E-DEBTOR)))
                                          [(intern! w (f e rw/E-BASE)) (f e rw/E-SEEN)]))})))
     :acts (tbl rw/T-ACT
                (fn [a] (let [c (f (f a rw/A-RUN) rw/R-OF)]
                          {:run (id (f a rw/A-RUN)) :mode (f a rw/A-MODE)
                           :members (vec (for [e (f c rw/C-INS) :when (identical? a (f e rw/E-ACT))]
                                           [(id e) (f e rw/E-SLOT)]))
                           :slots (mapv (fn [s] (when s (let [[v err?] s] [(if err? :err :ok) (intern! w v)])))
                                        (f a rw/A-SLOTS))
                           :remaining (f a rw/A-REMAINING)
                           :cont (intern! w (f a rw/A-R))})))
     :res {} :cleanup {} :pubs {} :forks {}
     :pins (into (sorted-map) (map (fn [[x n]] [(id x) n])) (f w rw/W-PINS))
     :pending-act nil
     :released false
     :next-id (aget ^longs (f w rw/W-NEXT) 0)}))

(defn projecting-hook
  "A world hook that attaches the projection to every log entry, and runs
   `inner` (e.g. the Rule R check)."
  ([] (projecting-hook nil))
  ([inner]
   (fn [w item]
     (let [^java.util.ArrayList log (f w rw/W-LOG)
           i (dec (.size log))]
       (.set log i (assoc (.get log i) :proj (projection w))))
     (when inner (inner w item)))))

(defn- opaque [w x]
  (cond (and (vector? x) (= :opaque (first x))) (intern! w (second x))
        (vector? x) (mapv #(opaque w %) x)
        :else x))

(defn log
  "The commit log; `[:opaque v]` payloads become interned Nats."
  [w] (mapv (fn [e] (update e :item #(opaque w %))) (f w rw/W-LOG)))
