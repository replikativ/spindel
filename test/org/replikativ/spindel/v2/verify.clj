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

(def ^:dynamic *reg* nil)

(defn- canon
  "M5: the world's current row for a reference (copies are registered by ID)."
  [x]
  (if (and *reg* (instance? (Class/forName "[Ljava.lang.Object;") x))
    (or (.get ^java.util.Map *reg* (aget ^objects x rw/ID)) x)
    x))

(defn- successors* [row]
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
                       (some-> (f row rw/R-SROW) list)
                       (f row rw/R-RES)))
    rw/T-ACT (let [x (f (f row rw/A-RUN) rw/R-OF)]
               (concat (when (== rw/T-COMP (t x))
                         (filter #(identical? row (f % rw/E-ACT)) (f x rw/C-INS)))
                       (filter #(and % (== rw/EK-WAIT (long (f % rw/E-KIND)))) (f row rw/A-MEMBERS))))
    rw/T-SCOPE (concat (some-> (f row rw/S-PARENT) list)
                       (keep #(f % rw/K-RUN) (.values ^java.util.Map (f row rw/S-TASKS))))
    rw/T-TASK (some-> (f row rw/K-RUN) list)
    rw/T-EDGE [(f row rw/E-DEBTOR)]
    nil))

(defn- successors [row] (map canon (successors* row)))

(declare live*)

(defn live
  "The least set containing the roots and closed under `successors`."
  [w]
  (binding [*reg* (f w rw/W-REG)]
  (live* w)))

(defn- live* [w]
  (let [reg (rows w)
        roots (map canon (concat [(f w rw/W-ROOT)]
                      ;; open explicit scopes (§3.1)
                      (filter #(and (== rw/T-SCOPE (t %)) (= :explicit (f % rw/S-KIND)) (f % rw/S-OPEN)) reg)
                      (map first (vals (f w rw/W-PINS)))
                      ;; observe edges, and host awaits (pending host promises)
                      (filter #(and (== rw/T-EDGE (t %))
                                    (let [k (long (f % rw/E-KIND))]
                                      (or (== k rw/EK-OBSERVE)
                                          (and (== k rw/EK-WAIT) (fn? (f % rw/E-CRED))))))
                              reg)))
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
    (loop [todo (vec (mapcat #(when (and (== rw/T-RUN (t %)) (== rw/ACT-DONE (long (f % rw/R-ACT))))
                                ;; the run row, its scope subtree, its entity as a tombstone
                                (concat (remove nil? [% (f % rw/R-SROW) (f % rw/R-OF)]) (f % rw/R-RES)))
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
    (into
     (vec (for [row (rows w)
                :when (not (.containsKey ^java.util.IdentityHashMap lv row))
                :when (not (admitted? row))]
            {:type (t row) :id (f row rw/ID)
             :idle (when (== rw/T-COMP (t row)) (f row rw/C-IDLE))}))
     ;; the reverse: a row the reference retains that the engine removed
     (let [reg (f w rw/W-REG)]
       (for [row (keys lv)
             :when (instance? (Class/forName "[Ljava.lang.Object;") row)
             :when (not (.containsKey ^java.util.Map reg (f row rw/ID)))]
         {:type (t row) :id (f row rw/ID) :removed true})))))

(defn checking-hook
  "A world hook that records Rule R divergences per commit into `acc`."
  [acc]
  (fn [w item]
    (let [v (violations w)]
      (when (seq v) (swap! acc conj {:item item :violations v})))))

;; ---------------------------------------------------------------------------
;; Projection of the engine state to the §2 tables (oracle input, §11.4)

(defn- intern! [w x] ((requiring-resolve 'org.replikativ.spindel.v2.core/intern-opaque!) w x))

(defn- id [row] (when row (f row rw/ID)))

(defn- result [w row]
  (when (some? (f row rw/C-DONE-EPOCH))
    [(if (f row rw/C-ERR) :err :ok) (intern! w (f row rw/C-RESULT))]))

(defn- owner-id
  "The owner's id, or nil once a scope owner is removed: Rule R's detach
   (Z#23, Z#25) leaves surviving rows without an owner."
  [w x]
  (when (and x (instance? (Class/forName "[Ljava.lang.Object;") x))
    (when (or (not= rw/T-SCOPE (t x)) (some? (.get ^java.util.Map (f w rw/W-REG) (id x))))
      (id x))))

(defn projection
  "{table {id row-map}} with §2 field names; nil is none."
  [w]
  (let [reg (rows w)
        by (group-by t reg)
        tbl (fn [type f] (into (sorted-map) (map (fn [r] [(id r) (f r)])) (get by type)))]
    {:scopes (merge
              ;; run scopes not materialized yet (their ids come from the run, Z#26 parent)
              (into {} (map (fn [r] (let [x (f r rw/R-OF)
                                          o (f x rw/OWNER)]
                                      [(f r rw/R-SCOPE)
                                       {:parent (when (and (== rw/T-TASK (t x)) (instance? (Class/forName "[Ljava.lang.Object;") o)
                                                           (== rw/T-SCOPE (t o)))
                                                  (id o))
                                        :kind :run :open true}])))
                    (get by rw/T-RUN))
              (tbl rw/T-SCOPE (fn [s] {:parent (id (f s rw/S-PARENT)) :kind (f s rw/S-KIND) :open (f s rw/S-OPEN)})))
     :tasks (tbl rw/T-TASK
                 (fn [k] {:owner (owner-id w (f k rw/OWNER)) :run (id (f k rw/K-RUN))
                          :inputs (mapv #(intern! w %) (f k rw/K-INPUTS))
                          :result (when (f k rw/K-DONE)
                                    [(if (f k rw/K-ERR) :err :ok) (intern! w (f k rw/K-RESULT))])
                          :handles (f k rw/HANDLES)}))
     :comps (tbl rw/T-COMP
                 (fn [c] {:owner (owner-id w (f c rw/OWNER)) :inputs (mapv #(intern! w %) (f c rw/C-INPUTS))
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
                         ;; the engine counts open regions; the model's list is opaque
                         :finalizers (vec (repeat (long (or (f r rw/R-FINS) 0)) 0))
                         :resources (mapv id (f r rw/R-RES))}))
     :sources (tbl rw/T-SOURCE
                   (fn [x] {:owner (owner-id w (f x rw/OWNER))
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
                (fn [a] (let [^objects ms (f a rw/A-MEMBERS)]
                          {:run (id (f a rw/A-RUN)) :mode (f a rw/A-MODE)
                           :members (vec (for [i (range (alength ms)) :let [e (aget ms i)] :when e]
                                           [(id e) i]))
                           :slots (mapv (fn [s] (when s (let [[v err?] s] [(if err? :err :ok) (intern! w v)])))
                                        (f a rw/A-SLOTS))
                           :remaining (f a rw/A-REMAINING)
                           :cont (intern! w (f a rw/A-R))})))
     :res (tbl rw/T-RES
               (fn [z] {:owner (id (f z rw/OWNER)) :kind (f z rw/Z-KIND) :at (f z rw/AT)
                        :phase (condp == (long (f z rw/Z-PHASE))
                                 rw/Z-ARMED :armed rw/Z-FIRED :fired rw/Z-CANCELLING :cancelling)}))
     :cleanup (into (sorted-map)
                    (keep (fn [r] (when (== rw/ACT-DONE (long (f r rw/R-ACT))) [(id r) {:rows []}])))
                    (get by rw/T-RUN))
     :pubs {} :forks {}
     :pins (into (sorted-map) (map (fn [[i [_ n]]] [i n])) (f w rw/W-PINS))
     :pending-act nil
     :released false
     :next-id (.get ^java.util.concurrent.atomic.AtomicLong (f w rw/W-NEXT))}))

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

(defn log
  "The commit log (opaque payloads are interned Nats already)."
  [w] (vec (f w rw/W-LOG)))

(defn gc-settle!
  "Forces collection so weak handles drop (T19), then waits for the world to
   process the drops (the census gate, §0)."
  [w]
  (dotimes [_ 3] (System/gc) (Thread/sleep 20))
  ((requiring-resolve 'org.replikativ.spindel.v2.core/call-in!) w (fn [] nil))
  (Thread/sleep 20)
  ((requiring-resolve 'org.replikativ.spindel.v2.core/call-in!) w (fn [] nil)))
