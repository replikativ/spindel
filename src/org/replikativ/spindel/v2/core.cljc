(ns org.replikativ.spindel.v2.core
  "Engine v2, layer 1 core (docs/engine-v2-spec.md).

   Scope so far: sources (signal, cell), computations, tasks with run scopes
   and structured cancellation, observe, pins, host waits, Rule R by
   retention counts.

   One world executes one slice at a time (D0). Every host entry takes the
   world gate, performs its transition, then drains: task starts,
   resumptions, eligible dispatches and Rule R, until nothing is left. Host
   callbacks run after the drain."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.rows :as rw
             #?@(:clj [:refer [g s! gl alist acount anth aadd! apop! aput! aclear! acopy]])]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.host :as hs]
            [is.simm.partial-cps.runtime :as pr]
            #?(:clj [is.simm.partial-cps.ioc :as ioc])
            #?(:clj [org.replikativ.spindel.engine.free-vars :as free-vars]))
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.rows :refer [g s! gl alist acount anth aadd! apop! aput! aclear! acopy]]
                            [org.replikativ.spindel.v2.core :refer [gated commit! rv]])))

#?(:clj (set! *warn-on-reflection* true))

(declare create-source-top-host! row-of world-of cancel-resource! demand! settle! pending-zero! rule-r! complete! validate!
         deliver-observe! value cancel! finish-task!)

;; ---------------------------------------------------------------------------
;; Execution context: the world being processed and the run holding the slice
;; on this thread (B6: continuations close over no engine object; F1: rows
;; hold no pointer to a world, the world is the one being processed).

#?(:clj (def ^ThreadLocal ctx-tl (ThreadLocal.))
   :cljs (def ctx-cell (doto (object-array 3) (aset 2 0))))

(defn- ctx ^objects []
  #?(:clj (let [c (.get ctx-tl)]
            (if (nil? c) (let [c (object-array 3)] (aset c 2 (num 0)) (.set ctx-tl c) c) c))
     :cljs ctx-cell))

(defn active-run [] (aget (ctx) 1))
(defn- set-active! [r] (aset (ctx) 1 r))

(defn cw
  "The world this thread is processing."
  [] (aget (ctx) 0))

(defn- enter-world!
  "Makes `w` the processed world; returns the previous one for `leave-world!`."
  [w]
  (let [c (ctx) prev (aget c 0)] (aset c 0 w) prev))

(defn- leave-world! [prev] (aset (ctx) 0 prev))

;; ---------------------------------------------------------------------------
;; World, ids, gate

(def ^:dynamic *world* nil)


(defn- alloc-id!
  "A fresh id from the family counter, shared by a world and its forks."
  ^long [w]
  #?(:clj (let [^java.util.concurrent.atomic.AtomicLong n (g w rw/W-NEXT)] (.getAndIncrement n))
     :cljs (let [n (g w rw/W-NEXT) id (aget n 0)] (aset n 0 (inc id)) id)))

(defn- peek-id ^long [w]
  #?(:clj (let [^java.util.concurrent.atomic.AtomicLong n (g w rw/W-NEXT)] (.get n))
     :cljs (aget (g w rw/W-NEXT) 0)))

(defn- register! [w row]
  (when-let [reg (g w rw/W-REG)]
    (hs/mput! reg (g row rw/ID) row))
  row)

(defn- unregister! [w row]
  (when-let [reg (g w rw/W-REG)]
    (hs/mdel! reg (g row rw/ID)))
  nil)

(defn- new-scope [w id kind parent]
  (let [s (rw/new-row (g w rw/W-EPOCH) rw/S-SIZE)]
    (s! s rw/TYPE rw/T-SCOPE)
    (s! s rw/ID id)
    (s! s rw/S-PARENT parent)
    (s! s rw/S-KIND kind)
    (s! s rw/S-OPEN true)
    (s! s rw/S-TASKS (hs/oset))
    (s! s rw/S-CHILDREN (alist))
    (when parent (aadd! (g parent rw/S-CHILDREN) s))
    (register! w s)))

(defn world
  "A new world. `:verify? true` keeps an id->row registry and a commit log
   (test only); `:hook` runs after every commit in verify mode."
  ([] (world {}))
  ([{:keys [verify? hook inline? budget executor] :or {inline? true budget 4096}}]
   (let [ep #?(:clj (Object.) :cljs (js-obj))
         w (rw/new-row ep rw/W-SIZE)
         next #?(:clj (java.util.concurrent.atomic.AtomicLong. 1)
                 :cljs (doto (long-array 1) (aset 0 1)))]
     (s! w rw/TYPE rw/T-WORLD)
     (s! w rw/W-EPOCH ep)
     (s! w rw/W-LOCK (hs/lock))
     (s! w rw/W-NEXT next)
     (s! w rw/W-READY (alist))
     (s! w rw/W-RESUME (alist))
     (s! w rw/W-START (alist))
     (s! w rw/W-CLEANUP (alist))
     (s! w rw/W-DRAINING false)
     (s! w rw/W-RQ (alist))
     (s! w rw/W-PINS (hs/vmap))
     (s! w rw/W-CALLBACKS (alist))
     (s! w rw/W-INGRESS (hs/mpsc))
     (s! w rw/W-SCHEDULED (hs/flag false))
     (s! w rw/W-EXEC (or executor (hs/executor)))
     (s! w rw/W-INLINE (boolean inline?))
     (s! w rw/W-BUDGET (long budget))
     (s! w rw/W-ROOTS (hs/lmap))
     (s! w rw/W-RELEASED false)
     (when verify?
       (s! w rw/W-REG (hs/lmap))
       (s! w rw/W-LOG (alist))
       (s! w rw/W-INTERN #?(:clj (let [n (long-array 1)] (aset n 0 2)   ; reserved: 1 ::cancelled, 2 ::closed
                                     [(doto (java.util.HashMap.) (.put ::cancelled 1) (.put ::closed 2)) (java.util.WeakHashMap.) n])
                       :cljs nil))
       (s! w rw/W-HOOK hook))
     (s! w rw/ID (alloc-id! w))
     (s! w rw/W-ROOT (new-scope w (alloc-id! w) :root nil))
     w)))

(declare host!)

#?(:clj
   (defmacro gated
     "H1: runs `body` as a host item of world `w`: directly when this thread
      already holds the world (a slice or a callback), else enqueued and
      processed per H2. Returns the body's value when it ran before return."
     [w & body]
     `(host! ~w (fn [] ~@body))))

(defn cancelled-ex
  "The error a cancelled entity's creditors and cleanup slices receive."
  [reason]
  (ex-info "cancelled" {:spindel/cancelled reason}))

(defn cancelled? [t] (some? (:spindel/cancelled (ex-data t))))

(defn closed-ex
  "The error a waiter on a closed source without a value receives (Z#53)."
  []
  (ex-info "source closed" {:spindel/closed true}))

#?(:clj
   (defmacro rv
     "M5: the world's view of the row a reference names (m5 design v3). An
      owned row is itself; others resolve through the world's forward map
      (stage 1b). Non-rows (callbacks, nil) pass through."
     [w x]
     (let [r (with-meta (gensym "r") {:tag 'objects})
           o (gensym "o")
           ww (with-meta (gensym "w") {:tag 'objects})
           h (with-meta (gensym "h") {:tag 'objects})
           i (gensym "i")
           cljs? (rw/cljs? &env)
           arr? (fn [v] (if cljs? `(cljs.core/array? ~v) `(instance? ~(symbol "[Ljava.lang.Object;") ~v)))
           ;; path compression: a reference read from a field of an owned row,
           ;; or from a list, is written back resolved, so later reads in this
           ;; world take the fast path (lists reached through owned rows and
           ;; world queues are this world's copies)
           field? (and (seq? x) (= 'g (first x)) (= 3 (count x)))
           elem? (and (seq? x) (= 'anth (first x)) (= 3 (count x)))
           slow (fn [write-back]
                  `(let [c# (resolve-row ~ww ~r)] ~write-back c#))]
       (cond
         field?
         `(let [~h ~(second x) ~o (aget ~h ~(nth x 2))]
            (if ~(arr? o)
              (let [~r ~o ~ww ~w]
                (if (identical? (aget ~r (unchecked-dec-int (alength ~r))) (aget ~ww rw/W-EPOCH))
                  ~r
                  (let [c# (resolve-row ~ww ~r)]
                    (when (identical? (aget ~h (unchecked-dec-int (alength ~h))) (aget ~ww rw/W-EPOCH))
                      (aset ~h ~(nth x 2) c#))
                    c#)))
              ~o))
         elem?
         `(let [l# ~(second x) ~i ~(nth x 2) ~o (anth l# ~i)]
            (if ~(arr? o)
              (let [~r ~o ~ww ~w]
                (if (identical? (aget ~r (unchecked-dec-int (alength ~r))) (aget ~ww rw/W-EPOCH))
                  ~r
                  (let [c# (resolve-row ~ww ~r)] (aput! l# ~i c#) c#)))
              ~o))
         :else
         `(let [~o ~x]
            (if ~(arr? o)
              (let [~r ~o ~ww ~w]
                (if (identical? (aget ~r (unchecked-dec-int (alength ~r))) (aget ~ww rw/W-EPOCH))
                  ~r
                  (resolve-row ~ww ~r)))
              ~o))))))

(declare own-copy!)

(defn resolve-row
  "M5: this world's copy of row `r`, made on first access (copy on access).
   The forward map is keyed by the stable row ID, so repeated forks never
   chain (design v3)."
  [w r]
  (let [^objects r r
        fwd (aget ^objects w rw/W-FWD)
        c (get fwd (aget r rw/ID))]
    (if (and c (identical? (aget ^objects c (unchecked-dec-int (alength ^objects c))) (aget ^objects w rw/W-EPOCH)))
      c
      (own-copy! w (or c r)))))

(defn- copy-containers!
  "The mutable containers of a copied row are copied too, so neither world
   mutates the other's (design v3 §4). Elements stay basis pointers; readers
   resolve them through rv."
  [^objects c]
  (let [t (long (aget c rw/TYPE))]
    (when (#{rw/T-COMP rw/T-TASK rw/T-SOURCE rw/T-RES} t)
      (aset c rw/OUTS (hs/lcopy (aget c rw/OUTS)))
      (aset c rw/HREF nil))                     ; handles are per world (design v3 §5)
    (condp == t
      rw/T-COMP (do (doseq [i [rw/C-INS rw/C-BASIS rw/C-ADOPT rw/C-ADOPT-BASE]]
                      (when-let [l (aget c i)] (aset c i (hs/lcopy l)))))
      rw/T-SOURCE (do (when (== rw/SRC-MAILBOX (long (aget c rw/X-KIND)))
                        (aset c rw/X-VALUE (hs/dcopy (aget c rw/X-VALUE))))
                      (when-let [q (aget c rw/X-WAITERS)] (aset c rw/X-WAITERS (hs/dcopy q))))
      rw/T-RUN (do (doseq [i [rw/R-RES rw/R-SCOPES]]
                     (when-let [l (aget c i)] (aset c i (hs/lcopy l))))
                   (when-let [m (aget c rw/R-ORD)] (aset c rw/R-ORD (hs/mcopy m))))
      rw/T-SCOPE (do (aset c rw/S-TASKS (hs/oset-copy (aget c rw/S-TASKS)))
                     (aset c rw/S-CHILDREN (hs/lcopy (aget c rw/S-CHILDREN)))
                     (when-let [l (aget c rw/S-SOURCES)] (aset c rw/S-SOURCES (hs/lcopy l))))
      rw/T-ACT (do (aset c rw/A-SLOTS (aclone ^objects (aget c rw/A-SLOTS)))
                   (aset c rw/A-MEMBERS (aclone ^objects (aget c rw/A-MEMBERS))))
      nil)
    c))

(defn- own-copy!
  "M5: copies a basis row into world `w`: stamps the epoch, copies its
   containers, records it in the forward map (and the verify registry)."
  [w ^objects r]
  (let [c (aclone r)]
    (aset c (unchecked-dec-int (alength c)) (aget ^objects w rw/W-EPOCH))
    (copy-containers! c)
    (aset ^objects w rw/W-FWD (assoc (aget ^objects w rw/W-FWD) (aget c rw/ID) c))
    (when-let [reg (aget ^objects w rw/W-REG)]
      (when (some? (hs/mget reg (aget c rw/ID))) (hs/mput! reg (aget c rw/ID) c)))
    c))

(defn- force! [x]
  (loop [x x]
    (if (pr/thunk? x) (recur (pr/force-thunk x)) x)))

;; ---------------------------------------------------------------------------
;; Commit log (verify mode only, §11.4)

(defn logging? [w] (some? (g w rw/W-LOG)))

(defn- by-identity? [x]
  (not (or (number? x) (string? x) (keyword? x) (symbol? x) (boolean? x) (char? x)
           (and (coll? x) (not (record? x))))))

(defn intern-opaque!
  "Verify mode: the Nat for an opaque value. Plain values intern by
   equality; identity objects (fns, arrays, handles) are held weakly, so the
   log retains nothing a body would not (census)."
  [w x]
  #?(:clj (if (nil? x)
            0
            (let [[^java.util.Map strong ^java.util.Map weak ^longs n] (g w rw/W-INTERN)
                  x (cond (cancelled? x) ::cancelled          ; reserved: 1 (see world)
                          (:spindel/closed (ex-data x)) ::closed   ; reserved: 2
                          :else x)
                  ^java.util.Map m (if (by-identity? x) weak strong)]
              (or (.get m x)
                  (let [v (aset n 0 (inc (aget n 0)))] (.put m x v) v))))
     :cljs 0))

(defn- opaque-item [w x]
  (cond (and (vector? x) (= :opaque (first x)) (== 2 (count x))) (intern-opaque! w (second x))
        ;; captures: element-wise, so equal captures (§1.6) give equal vectors
        (and (vector? x) (= :opaque-seq (first x)) (== 2 (count x)))
        (mapv #(intern-opaque! w %) (second x))
        (vector? x) (mapv #(opaque-item w %) x)
        :else x))

(defn log-commit! [w item0]
  (let [log (g w rw/W-LOG)
        item (opaque-item w item0)]
    (aadd! log {:item item :accepted true})
    (when-let [hook (g w rw/W-HOOK)] (hook w item)))
  nil)

#?(:clj
   (defmacro commit!
     "End of a transition: Rule R (§5.1), then the log entry in verify mode.
      The item form is only evaluated when logging."
     [w item]
     `(let [w# ~w]
        (rule-r! w#)
        (when (some? (g w# rw/W-LOG)) (log-commit! w# ~item))
        nil)))

(defn- refuse! [w item]
  (when-let [log (g w rw/W-LOG)]
    (aadd! log {:item item :accepted false}))
  nil)

;; ---------------------------------------------------------------------------
;; Status (§2)

(defn- comp? [row] (== rw/T-COMP (gl row rw/TYPE)))
(defn- task? [row] (== rw/T-TASK (gl row rw/TYPE)))
(defn- source? [row] (== rw/T-SOURCE (gl row rw/TYPE)))
(defn- act? [row] (== rw/T-ACT (gl row rw/TYPE)))
(defn- res? [row] (== rw/T-RES (gl row rw/TYPE)))

(defn- live? [c]
  (and (not (g c rw/C-IDLE))
       (some? (g c rw/C-DONE-EPOCH))
       (== (gl c rw/C-DONE-EPOCH) (gl c rw/C-EPOCH))
       (zero? (gl c rw/C-PENDING))))

(defn- current? [c r]
  (and (some? r) (== (gl r rw/R-EPOCH) (gl c rw/C-EPOCH))))

(defn- run-current?
  "A task run is always current; a computation run iff its epoch matches."
  [w r]
  (let [x (rv w (g r rw/R-OF))]
    (or (not (comp? x)) (current? x r))))

(defn- needs-run? [w c]
  (and (not (g c rw/C-IDLE))
       (not (and (some? (g c rw/C-DONE-EPOCH))
                 (== (gl c rw/C-DONE-EPOCH) (gl c rw/C-EPOCH))))
       (not (current? c (rv w (g c rw/C-RUN))))))

(defn- deferred? [d] (and (source? d) (== rw/SRC-DEFERRED (gl d rw/X-KIND))))
(defn- closed? [d] (and (source? d) (not (g d rw/X-OPEN))))

(defn- final?
  "D1, for the kinds implemented so far."
  [d]
  (cond (task? d) (boolean (g d rw/K-DONE))
        (closed? d) true
        (deferred? d) (pos? (gl d rw/VERSION))
        :else false))

(defn- settled?
  "A debtor whose result can be consumed now."
  [d]
  (cond (comp? d) (live? d)
        (task? d) (boolean (g d rw/K-DONE))
        (deferred? d) (pos? (gl d rw/VERSION))
        (res? d) (== rw/Z-FIRED (gl d rw/Z-PHASE))
        :else true))

(defn- hot? [row] (pos? (gl row rw/HOT)))

(declare blocked?)

(defn- eligible?
  "§4.5.7: every dirty computation debtor (a marked in-edge) has settled or
   is blocked."
  [w c]
  (or (zero? (gl c rw/C-PENDING))
      (let [ins (g c rw/C-INS)]
        (loop [i 0]
          (if (< i (acount ins))
            (let [e (rv w (anth ins i))]
              (if (and (g e rw/E-MARKED) (not (blocked? w (rv w (g e rw/E-DEBTOR)) 0)))
                false
                (recur (inc i))))
            true)))))

(defn- blocked?
  "§4.5.6, the least predicate: the entity's current run is parked and every
   unfilled member's debtor is a source or a blocked entity. A cycle is not
   blocked (a user deadlock)."
  [w x depth]
  (and (< (long depth) 64)
       (let [r (cond (comp? x) (let [r (rv w (g x rw/C-RUN))] (when (current? x r) r))
                     (task? x) (rv w (g x rw/K-RUN)))]
         (and r (== rw/ACT-PARKED (gl r rw/R-ACT))
              (let [a (rv w (g r rw/R-ACTV))
                    ^objects ms (when a (g a rw/A-MEMBERS))]
                (and ms
                     (loop [i 0 any? false]
                       (if (< i (alength ms))
                         (if-let [e (rv w (aget ms i))]
                           (let [d (rv w (g e rw/E-DEBTOR))]
                             (if (or (source? d) (res? d) (blocked? w d (inc (long depth))))
                               (recur (inc i) true)
                               false))
                           (recur (inc i) any?))
                         any?))))))))

(defn- maybe-schedule!
  "§4.5.7: a hot needs-run computation that is eligible is queued for
   dispatch."
  [w c]
  (when (and (needs-run? w c) (hot? c) (not (g c rw/C-QUEUED)) (eligible? w c))
    (s! c rw/C-QUEUED true)
    (aadd! (g w rw/W-READY) c)))

;; ---------------------------------------------------------------------------
;; Retention counts and demand (§3, §10.8, §10.10)

(defn- roots-map [w] (g w rw/W-ROOTS))

(defn- id-of ^long [x] (gl x rw/ID))

(defn- idx-of
  "Position of row `x` in list `l` by stable ID (M5: a list may hold the
   basis row while `x` is this world's copy)."
  ^long [l x]
  (let [id (id-of x) n (acount l)]
    (loop [i 0] (cond (== i n) -1 (== id (id-of (anth l i))) i :else (recur (inc i))))))

(defn- last-idx-of ^long [l x]
  (let [id (id-of x)]
    (loop [i (dec (acount l))] (cond (neg? i) -1 (== id (id-of (anth l i))) i :else (recur (dec i))))))

(defn- remove-row! [l x]
  (let [i (idx-of l x)] (when-not (neg? i) (hs/remove-at! l i) true)))

(defn- ref-inc! [row] (s! row rw/REFS (inc (gl row rw/REFS))))

(defn- ref-dec! [w row]
  (let [n (dec (gl row rw/REFS))]
    (s! row rw/REFS n)
    (when (zero? n) (aadd! (g w rw/W-RQ) row))))

(declare hot-inc! hot-dec!)

(defn- hot-inc! [w row]
  (let [h (inc (gl row rw/HOT))]
    (s! row rw/HOT h)
    (when (and (== h 1) (comp? row))
      (let [ins (g row rw/C-INS)]
        (dotimes [i (acount ins)] (hot-inc! w (rv w (g (rv w (anth ins i)) rw/E-DEBTOR)))))
      (maybe-schedule! w row))))

(defn- hot-dec! [w row]
  (let [h (dec (gl row rw/HOT))]
    (s! row rw/HOT h)
    (when (and (zero? h) (comp? row))
      (let [ins (g row rw/C-INS)]
        (dotimes [i (acount ins)] (hot-dec! w (rv w (g (rv w (anth ins i)) rw/E-DEBTOR))))))))

(defn- demands? [w e]
  (let [k (gl e rw/E-KIND)]
    (or (== k rw/EK-OBSERVE) (== k rw/EK-WAIT)
        (and (== k rw/EK-DEP) (hot? (rv w (g e rw/E-CRED)))))))

;; ---------------------------------------------------------------------------
;; Edges

(declare link-id!)

(defn- link!
  "A new edge on `debtor`. It retains the debtor (§3.2) and demands it when
   its creditor is demanded."
  [w kind cred debtor at]
  (link-id! w (alloc-id! w) kind cred debtor at))

(defn- link-id!
  "`link!` with an id allocated earlier (to keep the model's id order)."
  [w id kind cred debtor at]
  (let [e (rw/new-row (g w rw/W-EPOCH) rw/E-SIZE)
        outs (g debtor rw/OUTS)]
    (s! e rw/TYPE rw/T-EDGE)
    (s! e rw/ID id)
    (s! e rw/E-KIND kind)
    (s! e rw/E-CRED cred)
    (s! e rw/E-DEBTOR debtor)
    (s! e rw/E-AT at)
    (s! e rw/E-ARMED true)
    (s! e rw/E-MARKED false)
    (s! e rw/E-IDX (acount outs))
    (aadd! outs e)
    (ref-inc! debtor)
    (when (demands? w e) (hot-inc! w debtor))
    (when (or (== kind rw/EK-OBSERVE) (and (== kind rw/EK-WAIT) (fn? cred)))
      (s! e rw/E-ORIGIN (g w rw/ID))
      (hs/mput! (roots-map w) (id-of e) e))
    (register! w e)))

(defn- linked? [w e]
  (let [outs (g (rv w (g e rw/E-DEBTOR)) rw/OUTS)
        i (gl e rw/E-IDX)]
    (and (< i (acount outs)) (identical? e (rv w (anth outs i))))))

(defn- unmark! [w e]
  (when (g e rw/E-MARKED)
    (s! e rw/E-MARKED false)
    (let [c (rv w (g e rw/E-CRED))
          p (dec (gl c rw/C-PENDING))]
      (s! c rw/C-PENDING p)
      (when (zero? p) (pending-zero! w c)))))

(defn- unlink!
  "Removes an edge. A marked edge discharges its mark (X#1)."
  [w e]
  (let [debtor (rv w (g e rw/E-DEBTOR))
        outs (g debtor rw/OUTS)
        i (gl e rw/E-IDX)
        last-e (rv w (apop! outs))]
    (when-not (identical? last-e e)
      (aput! outs i last-e)
      (s! last-e rw/E-IDX i))
    (when (demands? w e) (hot-dec! w debtor))
    (s! e rw/E-ACT nil)
    (hs/mdel! (roots-map w) (id-of e))
    (unregister! w e)
    (unmark! w e)
    (ref-dec! w debtor)))

(defn- remove-dep!
  "Removes a dep edge from its computation's INS (T10, D2), keeping the
   running run's cursor on the same next site."
  [w e]
  (when (linked? w e)
  (let [c (rv w (g e rw/E-CRED))
        ins (g c rw/C-INS)
        i (idx-of ins e)]
    (when-not (neg? i)
      (hs/remove-at! ins i)
      (when-let [r (rv w (g c rw/C-RUN))]
        (when (> (gl r rw/R-CURSOR) i) (s! r rw/R-CURSOR (dec (gl r rw/R-CURSOR))))))
    (unlink! w e))))

;; ---------------------------------------------------------------------------
;; Mark and settle (§4.5)

(defn- mark-from!
  "§4.5.1: marks every dep out-edge of the computations reachable from `d`."
  [w d]
  (let [outs (g d rw/OUTS)]
    (dotimes [i (acount outs)]
      (let [e (rv w (anth outs i))]
        (when (and (== rw/EK-DEP (gl e rw/E-KIND)) (not (g e rw/E-MARKED)))
          (s! e rw/E-MARKED true)
          (let [c (rv w (g e rw/E-CRED))]
            (s! c rw/C-PENDING (inc (gl c rw/C-PENDING)))
            (mark-from! w c)))))))

(defn- invalidate!
  "A dep fire that is not a delivery (§4.5.3): an epoch step."
  [w e]
  (s! e rw/E-ARMED false)
  (let [c (rv w (g e rw/E-CRED))]
    (s! c rw/C-EPOCH (inc (gl c rw/C-EPOCH)))
    (mark-from! w c)
    (maybe-schedule! w c)))

(defn- debtor-result
  "[value err?] of a settled debtor."
  [d]
  (cond (comp? d) [(g d rw/C-RESULT) (boolean (g d rw/C-ERR))]
        (task? d) [(g d rw/K-RESULT) (boolean (g d rw/K-ERR))]
        (res? d) [(g d rw/Z-RESULT) (boolean (g d rw/Z-ERR))]
        (g d rw/X-OPEN) [(g d rw/X-VALUE) false]
        ;; Z#53: a closed source keeps a signal's or cell's value and a
        ;; delivered deferred's; a mailbox, a semaphore or an undelivered
        ;; deferred has none, so its waiters get an error
        (let [kind (gl d rw/X-KIND)]
          (or (== kind rw/SRC-MAILBOX) (== kind rw/SRC-SEMAPHORE)
              (and (== kind rw/SRC-DEFERRED) (zero? (gl d rw/VERSION)))))
        [(closed-ex) true]
        :else [(g d rw/X-VALUE) false]))

(defn- act-done? [a]
  (or (zero? (gl a rw/A-REMAINING)) (some? (g a rw/A-WINNER))))

(declare resume-at-fill!)

(defn- slot-fill!
  "Fills every slot whose member is `e` (Z#7). A complete activation that is
   not on the host stack is queued for resumption."
  [w a e res]
  (when-not (act-done? a)
    (let [^objects ms (g a rw/A-MEMBERS)
          ^objects sl (g a rw/A-SLOTS)
          n (alength ms)]
      (dotimes [i n]
        (when (identical? e (rv w (aget ms i)))
          (aset ms i nil)
          (aset sl i res)
          (s! a rw/A-REMAINING (dec (gl a rw/A-REMAINING)))
          (when (and (= :any (g a rw/A-MODE)) (nil? (g a rw/A-WINNER)))
            (s! a rw/A-WINNER i))))
      (when (act-done? a) (resume-at-fill! w a)))))

(defn- fill!
  "T9 delivery into the activation `a` that dep edge `e` is an unfilled
   member of."
  [w e a]
  (let [r (rv w (g a rw/A-RUN))
        d (rv w (g e rw/E-DEBTOR))]
    (when (and (run-current? w r) (== rw/ACT-PARKED (gl r rw/R-ACT)))   ; §4.5.4
      (s! e rw/E-ACT nil)
      (s! e rw/E-ARMED true)
      (s! e rw/E-SEEN (g d rw/VERSION))
      (slot-fill! w a e (debtor-result d)))))

(defn- fire-wait!
  "T9 on a wait edge: fills its activation's slot, or resolves the host
   promise; the edge is consumed (D2)."
  [w e]
  (let [cred (rv w (g e rw/E-CRED))
        d (rv w (g e rw/E-DEBTOR))
        res (debtor-result d)]
    (unlink! w e)
    (if (and (some? cred) (not (fn? cred)) (act? cred))
      (let [r (rv w (g cred rw/A-RUN))]
        (when (and (identical? cred (rv w (g r rw/R-ACTV))) (run-current? w r)
                   (== rw/ACT-PARKED (gl r rw/R-ACT)))
          (slot-fill! w cred e res)))
      (when (= (g e rw/E-ORIGIN) (g w rw/ID))         ; Z#45
        (aadd! (g w rw/W-CALLBACKS) [cred res])))))

(defn- fire-dep!
  "T9 on a dep edge whose debtor changed."
  [w e]
  (when (g e rw/E-ARMED)
    (let [a (g e rw/E-ACT)]
      (if (and a (run-current? w (rv w (g a rw/A-RUN))))
        (fill! w e a)
        (invalidate! w e)))))

(defn- settle!
  "§4.5.2: `d` became live (or final). Changed out-edges fire before they
   are unmarked; unfilled members of a current activation are delivered
   either way (Z#20). Wait edges are consumed."
  [w d]
  (when (pos? (acount (g d rw/OUTS)))
  (let [outs (acopy (g d rw/OUTS))
        ver (g d rw/VERSION)]
    (dotimes [i (acount outs)]
      (let [e (rv w (anth outs i))
            k (gl e rw/E-KIND)]
        (cond
          (== k rw/EK-DEP)
          (do (if-let [a (g e rw/E-ACT)]
                (fill! w e a)
                (when (not= ver (g e rw/E-SEEN)) (fire-dep! w e)))
              (unmark! w e))
          (== k rw/EK-OBSERVE) (deliver-observe! w e)
          (== k rw/EK-WAIT) (fire-wait! w e))))
    ;; T10: dep edges on a final debtor are removed after their delivery.
    (when (and (final? d) (pos? (acount (g d rw/OUTS))))
      (let [outs (acopy (g d rw/OUTS))]
        (dotimes [i (acount outs)]
          (let [e (rv w (anth outs i))]
            (when (and (== rw/EK-DEP (gl e rw/E-KIND)) (g e rw/E-ARMED) (nil? (g e rw/E-ACT)))
              (remove-dep! w e)))))))))

(defn- pending-zero! [w c]
  (cond
    (live? c) (settle! w c)
    :else (maybe-schedule! w c)))

;; ---------------------------------------------------------------------------
;; Observe delivery (§4.2)

(defn- deliver-observe! [w e]
  (let [d (rv w (g e rw/E-DEBTOR))
        ver (g d rw/VERSION)
        seen (g e rw/E-SEEN)]
    (when (and (settled? d) (or (nil? seen) (> (long ver) (long seen))))
      (s! e rw/E-SEEN ver)
      ;; Z#45: an observe edge a fork inherited keeps its demand, but its
      ;; callback belongs to the parent's host and is not called here
      (when (= (g e rw/E-ORIGIN) (g w rw/ID))
        (aadd! (g w rw/W-CALLBACKS) [(rv w (g e rw/E-CRED)) (debtor-result d)])))))

;; ---------------------------------------------------------------------------
;; Runs and scopes

(defn- new-run! [w x epoch]
  (let [r (rw/new-row (g w rw/W-EPOCH) rw/R-SIZE)]
    (s! r rw/TYPE rw/T-RUN)
    (s! r rw/ID (alloc-id! w))
    (s! r rw/R-SCOPE (alloc-id! w))          ; run scope id; T4/T5/T11 order: run, scope
    (s! r rw/R-OF x)
    (s! r rw/R-EPOCH epoch)
    (s! r rw/R-ACT rw/ACT-ACTIVE)
    (s! r rw/R-MODE 0)
    (s! r rw/R-SLICE false)
    (s! r rw/R-EIDX 0)
    (s! r rw/R-CURSOR 0)
    (if (comp? x) (s! x rw/C-RUN r) (s! x rw/K-RUN r))
    (register! w r)))

(defn- run-scope!
  "The run scope row of `r`, materialized on first use (Z#26 parent rule)."
  [w r]
  (or (rv w (g r rw/R-SROW))
      (let [x (rv w (g r rw/R-OF))
            owner (rv w (g x rw/OWNER))
            parent (when (and (task? x) owner (== rw/T-SCOPE (gl owner rw/TYPE))) owner)
            s (new-scope w (g r rw/R-SCOPE) :run parent)]
        (s! s rw/S-HELD true)
        (s! r rw/R-SROW s)
        s)))

(defn- current-scope!
  "The innermost open explicit scope of the run, else its run scope."
  [w r]
  (let [ss (g r rw/R-SCOPES)]
    (if (and ss (pos? (acount ss)))
      (rv w (anth ss (dec (acount ss))))
      (run-scope! w r))))

(defn- remove-scope-if-empty!
  "T16/Z#18: a closed scope row goes once its subtree has no rows left. A run
   scope stays while its run is in cleanup (T13 step 4, Z#52)."
  [w s]
  (when (and (not (g s rw/S-OPEN))
             (not (g s rw/S-HELD))
             (zero? (hs/oset-count (g s rw/S-TASKS)))
             (zero? (acount (g s rw/S-CHILDREN))))
    (unregister! w s)
    (when-let [p (rv w (g s rw/S-PARENT))]
      (let [cs (g p rw/S-CHILDREN)
            i (idx-of cs s)]
        (when-not (neg? i) (hs/remove-at! cs i))
        (remove-scope-if-empty! w p)))))

(declare close-source!)

(defn- close-scope!
  "T16: cancels the work owned by the subtree, closes its scopes and the
   sources they own."
  [w s]
  (when (g s rw/S-OPEN)
    (s! s rw/S-OPEN false)
    (when-let [xs (g s rw/S-SOURCES)]
      (s! s rw/S-SOURCES nil)
      (dotimes [i (acount xs)]
        (when-let [x (hs/deref-weak (rv w (anth xs i)))] (close-source! w x))))
    (let [ts (hs/oset-vals (g s rw/S-TASKS))]
      (doseq [t ts]
        (when-let [r (rv w (g t rw/K-RUN))] (cancel! w r ::cancelled))))
    (let [cs (acopy (g s rw/S-CHILDREN))]
      (dotimes [i (acount cs)] (close-scope! w (rv w (anth cs i))))))
  (remove-scope-if-empty! w s))

(defn- retire!
  "T13, in Z#18 order."
  [w r]
  (let [x (rv w (g r rw/R-OF))]
    (if (comp? x)
      (when (identical? r (rv w (g x rw/C-RUN))) (s! x rw/C-RUN nil))
      (when (identical? r (rv w (g x rw/K-RUN))) (s! x rw/K-RUN nil)))
    (s! r rw/R-MODE 2)                       ; retired
    (when-let [s (rv w (g r rw/R-SROW))]
      (s! s rw/S-HELD false)
      (close-scope! w s))
    (unregister! w r)))

(defn- fins ^long [r] (let [n (g r rw/R-FINS)] (if n (long n) 0)))

(defn- retire-check!
  "T13: retired iff done, no slice, no finalizers, no resources."
  [w r]
  (when (and (== rw/ACT-DONE (gl r rw/R-ACT)) (not (g r rw/R-SLICE))
             (zero? (fins r)) (nil? (g r rw/R-RES)) (not (== 2 (gl r rw/R-MODE))))
    (retire! w r)))

(defn- release-members!
  "An activation is removed: dep members stay with the computation (W#2),
   wait members are removed with it (D2)."
  [w a]
  (let [^objects ms (g a rw/A-MEMBERS)]
    (dotimes [i (alength ms)]
      (when-let [e (rv w (aget ms i))]
        (aset ms i nil)
        (if (== rw/EK-DEP (gl e rw/E-KIND))
          (s! e rw/E-ACT nil)
          (when (linked? w e) (unlink! w e))))))
  (unregister! w a))

(defn- drop-activation! [w r]
  (when-let [a (rv w (g r rw/R-ACTV))]
    (s! r rw/R-ACTV nil)
    ;; a savepoint activation leaves the pending set: its publication can no
    ;; longer resume the run
    (when-let [sps (g w rw/W-SAVEPOINTS)] (hs/oset-del! sps (id-of a)))
    (release-members! w a)
    a))

(defn- cancel!
  "T14 `cancel(R)`. Also `cancel(R, replace)` (Y#2): only T11 and demotion
   issue a replace, always on a computation run, which has no debtor side, so
   it is the same operation; on a task run a replace is an ordinary cancel."
  [w r reason]
  (when-not (== rw/ACT-DONE (gl r rw/R-ACT))
    (s! r rw/R-ACT rw/ACT-DONE)
    (s! r rw/R-MODE 1)
    ;; Finalizers (T14, B3): a parked run with open finally regions unwinds
    ;; in a cleanup slice through its activation's error continuation. A run
    ;; whose slice is on the stack unwinds at its next effect.
    (when-let [a (drop-activation! w r)]
      (when (pos? (fins r))
        (aadd! (g w rw/W-CLEANUP) [r (g a rw/A-E) (cancelled-ex reason)])))
    ;; Resources are told to cancel; they join through their acknowledgement.
    (when-let [zs (g r rw/R-RES)]
      (doseq [z (vec zs)] (cancel-resource! w z)))
    ;; children: runs owned by the run scope
    (when-let [s (rv w (g r rw/R-SROW))]
      (let [ts (hs/oset-vals (g s rw/S-TASKS))]
        (doseq [t ts]
          (when-let [cr (rv w (g t rw/K-RUN))] (cancel! w cr reason)))))
    (let [x (rv w (g r rw/R-OF))]
      (when (task? x)
        ;; debtor side (R#14): the task fails with ::cancelled
        (finish-task! w x (cancelled-ex reason) true)))
    (retire-check! w r)))

(defn- slice!
  "Runs `f` as a slice of `r` on the host stack, restoring the caller's
   active run afterwards (I10)."
  [r f]
  (let [prev (active-run)
        c (ctx)]
    (s! r rw/R-SLICE true)
    (set-active! r)
    (aset c 2 #?(:clj (num (inc (long (aget c 2)))) :cljs (inc (aget c 2))))
    (try
      (try (force! (f))
           (catch #?(:clj Throwable :cljs :default) t
             (complete! (or (active-run) r) t true)))
      (finally
        ;; re-resolve: a fork effect in this slice made `r` a shared basis row
        (aset c 2 #?(:clj (num (dec (long (aget c 2)))) :cljs (dec (aget c 2))))
        (let [w (cw) r (rv w r)]
          ;; a done run whose slice still holds the flag (a cleanup slice, or a
          ;; cancelled run unwinding) returns here: an explicit item
          ;; (Z#49); T13 retires it within that item, as T12 does (Z#34)
          (if (and (g r rw/R-SLICE) (== rw/ACT-DONE (gl r rw/R-ACT)))
            (do (s! r rw/R-SLICE false)
                (set-active! prev)
                (retire-check! w r)
                (commit! w [:slice-exit (g r rw/ID)]))
            (do (s! r rw/R-SLICE false)
                (set-active! prev)
                (retire-check! w r))))))))

(defn- ok-k [v] (complete! (active-run) v false))
(defn- err-k [t] (complete! (active-run) t true))

(defn- release-adoption! [w c]
  (when-let [ab (g c rw/C-ADOPT)]
    (s! c rw/C-ADOPT nil)
    (dotimes [i (acount ab)]
      (let [x (rv w (anth ab i))]
        ;; §5.2: a task the new run did not re-spawn is cancelled
        (when (and (task? x) (rv w (g x rw/K-RUN))) (cancel! w (rv w (g x rw/K-RUN)) ::cancelled))
        (ref-dec! w x))))
  (when-let [bs (g c rw/C-ADOPT-BASE)]
    (s! c rw/C-ADOPT-BASE nil)
    (dotimes [i (acount bs)] (ref-dec! w (rv w (g (rv w (anth bs i)) rw/E-DEBTOR))))))

(defn- finish-task!
  "Sets a task's result and fires its creditors; ownership retention ends."
  [w k v err?]
  (when-not (g k rw/K-DONE)
    (s! k rw/K-DONE true)
    (s! k rw/K-RESULT v)
    (s! k rw/K-ERR (boolean err?))
    (s! k rw/VERSION (inc (gl k rw/VERSION)))
    (settle! w k)
    (let [owner (rv w (g k rw/OWNER))]
      (when (and owner (not (fn? owner)) (== rw/T-SCOPE (gl owner rw/TYPE)))
        (when (hs/oset-del! (g owner rw/S-TASKS) (id-of k))
          (ref-dec! w k))
        (do
          (remove-scope-if-empty! w owner))))))

(defn- complete!
  "T12."
  [r v err?]
  (when (and r (== rw/ACT-ACTIVE (gl r rw/R-ACT)))
    (let [w (cw)
          x (rv w (g r rw/R-OF))]
      (s! r rw/R-ACT rw/ACT-DONE)
      (if (comp? x)
        (do
          (when (current? x r)
            (let [changed? (or (nil? (g x rw/C-DONE-EPOCH))
                               (not= (boolean err?) (boolean (g x rw/C-ERR)))
                               (not= v (g x rw/C-RESULT)))]
              (when changed?
                (s! x rw/VERSION (inc (gl x rw/VERSION)))
                (s! x rw/C-RESULT v)
                (s! x rw/C-ERR (boolean err?)))
              (s! x rw/C-DONE-EPOCH (g r rw/R-EPOCH))
              (release-adoption! w x)))
          (when (live? x) (settle! w x))
          ;; T12 includes slice exit (the model folds it): retire now if allowed
          (s! r rw/R-SLICE false)
          (retire-check! w r)
          (commit! w [:complete (g r rw/ID) (if err? 2 1) [:opaque v]]))
        (do
          ;; Q10: children not awaited and not detached are cancelled
          (when-let [s (rv w (g r rw/R-SROW))]
            (let [ts (hs/oset-vals (g s rw/S-TASKS))]
              (doseq [t ts]
                (when-let [cr (rv w (g t rw/K-RUN))] (cancel! w cr ::cancelled)))))
          (finish-task! w x v err?)
          (s! r rw/R-SLICE false)
          (retire-check! w r)
          (commit! w [:complete (g r rw/ID) (if err? 2 1) [:opaque v]])))))
  nil)

;; ---------------------------------------------------------------------------
;; Dispatch (T5, T11)

(defn- earliest-fired [w c]
  (let [ins (g c rw/C-INS)]
    (loop [i 0]
      (when (< i (acount ins))
        (let [e (rv w (anth ins i))]
          (if (g e rw/E-ARMED) (recur (inc i)) i))))))

(defn- restore-ordinals! [w c r]
  (when-let [basis (g c rw/C-BASIS)]
    (when (pos? (acount basis))
      (let [ords (hs/vmap)]
        (dotimes [i (acount basis)]
          (let [key (gl (rv w (anth basis i)) rw/KEY)
                site (quot key 1048576)
                nxt (inc (mod key 1048576))
                cur (long (or (hs/mget ords site) 0))]
            (when (> nxt cur) (hs/mput! ords site nxt))))
        (s! r rw/R-ORD ords)))))

(defn- dispatch!
  "T11 (and T5 for a computation without a fired edge): starts the
   computation's next run, re-entering at its earliest fired dep edge when
   that site is re-entrant (X#2)."
  [w c]
  (s! c rw/C-QUEUED false)
  (when (needs-run? w c)
    (when-let [old (rv w (g c rw/C-RUN))] (cancel! w old ::cancelled))
    (let [ins (g c rw/C-INS)
          restart? (g c rw/C-RESTART)
          ei (when-not restart? (earliest-fired w c))
          e (when ei (rv w (anth ins ei)))
          at (if e (gl e rw/E-AT) -1)]
      (s! c rw/C-RESTART false)
      ;; Suffix: dep edges after E keep their debtors through the adoption
      ;; baselines (§4.4, Z#21).
      (let [keep (if ei (inc (long ei)) (if restart? 0 (acount ins)))]
        (when (> (acount ins) keep)
          (let [bs (or (g c rw/C-ADOPT-BASE) (alist))]
            (loop []
              (when (> (acount ins) keep)
                (let [x (rv w (apop! ins))]
                  (ref-inc! (rv w (g x rw/E-DEBTOR)))
                  (aadd! bs x)
                  (unlink! w x))
                (recur)))
            (s! c rw/C-ADOPT-BASE bs))))
      ;; Suffix creations become the adoption basis.
      (let [basis (g c rw/C-BASIS)]
        (when (and basis (pos? (acount basis)))
          (let [ab (or (g c rw/C-ADOPT) (alist))
                kept (alist)]
            (dotimes [i (acount basis)]
              (let [x (rv w (anth basis i))]
                (if (or restart? (> (gl x rw/AT) at)) (aadd! ab x) (aadd! kept x))))
            (s! c rw/C-BASIS kept)
            (s! c rw/C-ADOPT ab))))
      (let [t5? (and (nil? e) (zero? (acount ins)))
            r (new-run! w c (g c rw/C-EPOCH))
            k (when e (g e rw/E-CONT))
            ;; E is consumed in this commit (T11): re-armed with its delivery
            go (if (and e k)
                 (let [d (rv w (g e rw/E-DEBTOR))]
                   (restore-ordinals! w c r)
                   (s! r rw/R-CURSOR (inc (long ei)))
                   (s! r rw/R-EIDX (inc at))
                   (s! e rw/E-ARMED true)
                   (s! e rw/E-SEEN (g d rw/VERSION))
                   (if (source? d)
                     (let [old (g e rw/E-BASE) v (g d rw/X-VALUE)]
                       (s! e rw/E-BASE v)
                       #(k (iv/->Interval old v nil)))
                     (let [[v err?] (debtor-result d)
                           ek (g e rw/E-ERRK)]
                       (when (final? d) (remove-dep! w e))   ; consumed: removed, not re-armed
                       (if err? #(ek v) #(k v)))))
                 ;; Restart from the body. E (if any) is re-armed (removed if its
                 ;; debtor is final); its baseline advances when the new run reads
                 ;; it (Z#22).
                 (do (when e
                       (if (final? (rv w (g e rw/E-DEBTOR))) (remove-dep! w e) (s! e rw/E-ARMED true)))
                     #((g c rw/C-BODY) ok-k err-k)))]
        (commit! w [(if t5? :start :dispatch) (g c rw/ID) (g r rw/ID)])
        ;; the new run's first slice is a scheduling choice (D0)
        (s! r rw/R-SLICE true)
        (commit! w [:schedule (g r rw/ID)])
        (slice! r go)))))

;; ---------------------------------------------------------------------------
;; Body effects

(defn- valid-run
  "The active run if an effect token is valid (§2): the run exists, holds the
   slice and is not done."
  []
  (let [r (active-run)]
    (when-not r (throw (ex-info "effect outside a body" {})))
    (when (and (g r rw/R-SLICE) (not (== rw/ACT-DONE (gl r rw/R-ACT)))) r)))

(defn- unwind!
  "An effect of a cancelled run: with open finally regions the body unwinds
   through `ek` (the cleanup continues in this slice, B8); otherwise the
   continuation is dropped (L4)."
  [ek]
  (let [r (active-run)]
    (when (and r (g r rw/R-SLICE) (== rw/ACT-DONE (gl r rw/R-ACT)) (pos? (fins r)))
      (ek (cancelled-ex ::cancelled)))))

(defn- next-at! ^long [r]
  (let [at (gl r rw/R-EIDX)]
    (s! r rw/R-EIDX (inc at))
    at))

(defn- adoption-baseline!
  "Consumes a suffix baseline for (at, d) (§4.4)."
  [w c at d]
  (when-let [bs (g c rw/C-ADOPT-BASE)]
    (loop [i 0]
      (when (< i (acount bs))
        (let [x (rv w (anth bs i))]
          (if (and (== at (gl x rw/E-AT)) (identical? d (rv w (g x rw/E-DEBTOR))))
            (do (aput! bs i (rv w (anth bs (dec (acount bs)))))
                (apop! bs)
                (ref-dec! w d)
                x)
            (recur (inc i))))))))

(defn- raise-rank!
  "I12 by height adjustment: `c` must rank above `d`. Raising propagates to
   c's creditors; reaching `d` again means the new edge closes a cycle."
  [w c d]
  (let [need (inc (gl d rw/C-RANK))]
    (if (>= (gl c rw/C-RANK) need)
      true
      (loop [todo [[c need]] seen #{}]
        (if-let [[x n] (peek todo)]
          (let [todo (pop todo)]
            (cond
              (identical? x d) false
              (>= (gl x rw/C-RANK) (long n)) (recur todo seen)
              :else
              (do (s! x rw/C-RANK n)
                  (let [outs (g x rw/OUTS)]
                    (recur (loop [i 0 todo todo]
                             (if (< i (acount outs))
                               (let [e (rv w (anth outs i))]
                                 (recur (inc i)
                                        (if (== rw/EK-DEP (gl e rw/E-KIND))
                                          (conj todo [(rv w (g e rw/E-CRED)) (inc (long n))])
                                          todo)))
                               todo))
                           seen)))))
          true)))))

(defn cycle-ex [c d]
  (ex-info "dependency cycle" {:spindel/cycle [(g c rw/ID) (g d rw/ID)]}))

(defn- site-edge!
  "The dep edge of `c` at site `at` on `d`: reused when the prefix already
   has it, otherwise created. Returns [edge reused?]. A new edge that would
   close a computation cycle is refused (I12): returns [nil false]."
  [w r c d at k ek]
  (let [ins (g c rw/C-INS)
        cur (gl r rw/R-CURSOR)]
    (s! r rw/R-CURSOR (inc cur))
    (if (and (< cur (acount ins))
             (== at (gl (rv w (anth ins cur)) rw/E-AT))
             (identical? d (rv w (g (rv w (anth ins cur)) rw/E-DEBTOR))))
      (let [e (rv w (anth ins cur))]
        (s! e rw/E-CONT k) (s! e rw/E-ERRK ek)
        [e true])
      (do (loop []                              ; a diverged prefix: drop the rest
            (when (> (acount ins) cur) (unlink! w (rv w (apop! ins))) (recur)))
          (if (and (comp? d) (or (identical? c d) (not (raise-rank! w c d))))
            (do (s! r rw/R-CURSOR cur) [nil false])
            (let [e (link! w rw/EK-DEP c d at)]
              (s! e rw/E-CONT k) (s! e rw/E-ERRK ek)
              (aadd! ins e)
              [e false]))))))

(defn- reentrant-k
  "§2: `cont` is the continuation only for `one` awaits in a run without
   finalizers or resources."
  [r k]
  (when (and (zero? (fins r)) (nil? (g r rw/R-RES))) k))

(defn enter-finally!
  "Body contract: a `finally` region opens (rewritten by the body macros)."
  []
  (when-let [r (active-run)]
    (s! r rw/R-FINS (inc (fins r)))
    (commit! (cw) [:finally-enter (g r rw/ID)])))

(defn exit-finally!
  "A `finally` region closes; its block runs now."
  []
  (when-let [r (active-run)]
    (s! r rw/R-FINS (max 0 (dec (fins r))))
    (commit! (cw) [:finally-exit (g r rw/ID)])))

(defn- invalid-op [op msg] (ex-info msg {:spindel/invalid op}))

(defn track-effect!
  "T7, on signals and cells (Z#54)."
  [x k ek]
  (if-not (and (source? x) (<= (gl x rw/X-KIND) rw/SRC-CELL))
    (ek (invalid-op :track "track is for signals and cells"))
  (if-let [r (valid-run)]
    (let [w (cw)
          c (rv w (g r rw/R-OF))
          at (next-at! r)]
      (if-not (comp? c)
        ;; Inside a task: a snapshot read with no edge (Q1, Z#19).
        (do (commit! w [:track (g r rw/ID) (g x rw/ID) [:opaque k] 0])
            (k (iv/->Interval nil (g x rw/X-VALUE) nil)))
        (let [[e reused?] (site-edge! w r c x at (reentrant-k r k) ek)
              v (g x rw/X-VALUE)
              old (if reused?
                    (g e rw/E-BASE)
                    (when-let [b (adoption-baseline! w c at x)] (g b rw/E-BASE)))]
          (s! e rw/E-BASE v)
          (s! e rw/E-SEEN (g x rw/VERSION))
          (s! e rw/E-ARMED true)
          ;; Z#48: a closed (final) source delivers once; its edge is consumed
          (when (final? x) (remove-dep! w e))
          (commit! w [:track (g r rw/ID) (g x rw/ID) [:opaque k] (if reused? 0 (g e rw/ID))])
          (k (iv/->Interval old v nil)))))
    (unwind! ek))))

(defn- new-activation! [w aid r mode k ek ^objects members ^objects slots remaining]
  (let [a (rw/new-row (g w rw/W-EPOCH) rw/A-SIZE)]
    (s! a rw/TYPE rw/T-ACT)
    (s! a rw/ID aid)
    (s! a rw/A-RUN r)
    (s! a rw/A-MODE mode)
    (s! a rw/A-SLOTS slots)
    (s! a rw/A-MEMBERS members)
    (s! a rw/A-REMAINING remaining)
    (s! a rw/A-R k)
    (s! a rw/A-E ek)
    (s! a rw/A-INLINE true)
    (register! w a)))

(defn- park! [r a]
  (s! r rw/R-ACTV a)
  (s! r rw/R-ACT rw/ACT-PARKED)
  (s! r rw/R-SLICE false))

(defn- group-result
  "The delivery of a complete activation: `one` its slot, `all` the vector of
   values (or the first error in slot order), `any` the winning slot."
  [mode ^objects slots winner]
  (case mode
    :one (aget slots 0)
    :any (aget slots (int winner))
    :all (let [n (alength slots)]
           (loop [i 0 acc (transient [])]
             (if (< i n)
               (let [[v err?] (aget slots i)]
                 (if err? [v true] (recur (inc i) (conj! acc v))))
               [(persistent! acc) false])))))

(defn- continue! [res k ek]
  (let [[v err?] res] (if err? (ek v) (k v))))

(defn- cancel-losers!
  "`any` in a task run: loser tasks created by the run, with no other
   creditor, are cancelled (T6)."
  [w r ^objects members]
  (let [s (rv w (g r rw/R-SROW))]
    (dotimes [i (alength members)]
      (when-let [e (rv w (aget members i))]
        (let [d (rv w (g e rw/E-DEBTOR))]
          (when (and s (task? d) (identical? s (rv w (g d rw/OWNER)))
                     (== 1 (acount (g d rw/OUTS))) (rv w (g d rw/K-RUN)))
            (cancel! w (rv w (g d rw/K-RUN)) ::cancelled)))))))

(defn- resume-at-fill!
  "T6/T9: a complete activation resumes its run in the filling commit: the
   activation goes, the run becomes active, and its slice waits for a
   scheduling choice ([:schedule r]). An activation whose awaiting frame is
   still on the host stack continues there instead (I10)."
  [w a]
  (let [r (rv w (g a rw/A-RUN))]
    (s! r rw/R-ACTV nil)
    (s! r rw/R-ACT rw/ACT-ACTIVE)
    (when (and (= :any (g a rw/A-MODE)) (not (comp? (rv w (g r rw/R-OF)))))
      (cancel-losers! w r (g a rw/A-MEMBERS)))
    (release-members! w a)
    (s! a rw/A-RESULT (group-result (g a rw/A-MODE) (g a rw/A-SLOTS) (g a rw/A-WINNER)))
    (s! a rw/A-RESUMED true)
    (when-not (g a rw/A-INLINE)
      (aadd! (g w rw/W-RESUME) a))))

(defn- notify-blocked!
  "§4.5.6-7: `x` parked. Creditors with a marked edge from it may now be
   eligible, and entities parked on it may now be blocked in turn."
  [x depth]
  (when (< (long depth) 64)
    (let [w (cw)
          outs (g x rw/OUTS)]
      (dotimes [i (acount outs)]
        (let [e (rv w (anth outs i))
              k (gl e rw/E-KIND)]
          (cond
            (== k rw/EK-DEP)
            (let [c (rv w (g e rw/E-CRED))]
              (when (g e rw/E-MARKED) (maybe-schedule! w c))
              (when (g e rw/E-ACT) (notify-blocked! c (inc (long depth)))))
            (== k rw/EK-WAIT)
            (let [a (rv w (g e rw/E-CRED))]
              (when (and (some? a) (not (fn? a)) (act? a))
                (notify-blocked! (rv w (g (rv w (g a rw/A-RUN)) rw/R-OF)) (inc (long depth)))))))))))

(defn- mine-of
  "The `any` loser candidates of an await (T6): member tasks the run created
   (owned by its run scope)."
  [w r ds]
  (let [s (rv w (g r rw/R-SROW))]
    (vec (for [d ds :let [d (row-of d)]
               :when (and (task? d) s (identical? s (rv w (g d rw/OWNER))))]
           (g d rw/ID)))))

(defn- await-group!
  "T6: an activation over `ds` with `mode` (:one :all :any)."
  [ds mode k ek]
  (if-not (valid-run)
    (unwind! ek)
  (let [r (valid-run)]
    (let [w (cw)
          x (rv w (g r rw/R-OF))
          at (next-at! r)
          aid (alloc-id! w)
          n (count ds)
          members (object-array n)
          slots (object-array n)
          in-comp? (comp? x)
          refused (volatile! nil)
          ;; group sites restart (Y#3); `one` sites re-enter when allowed (§2)
          kk (when (= mode :one) (reentrant-k r k))]
      ;; Reactivation of valid idle debtors first, then member edges in
      ;; debtor-list order (the model's allocation order).
      (dotimes [i n]
        (let [d (row-of (nth ds i))]
          (when (and (comp? d) (g d rw/C-IDLE)) (validate! w d))))
      ;; Member edges; a repeated debtor shares its edge.
      (dotimes [i n]
        (let [d (row-of (nth ds i))
              prev (loop [j 0] (when (< j i)
                                 (let [m (rv w (aget members j))]
                                   (if (and m (identical? d (rv w (g m rw/E-DEBTOR)))) m (recur (inc j))))))]
          (cond
            prev (aset members i prev)
            in-comp? (let [[e _] (site-edge! w r x d at kk ek)]
                       (if (nil? e)
                         (vreset! refused d)
                         (do (when (and (source? d) (not (deferred? d))) (s! e rw/E-BASE (g d rw/X-VALUE)))
                             (aset members i e))))
            (and (source? d) (not (deferred? d))) nil       ; a task reads a signal once
            (settled? d) (alloc-id! w)                      ; consumed at once (Z#28)
            :else (aset members i (link! w rw/EK-WAIT nil d at)))))
      (if-let [d @refused]
        (do (refuse! w [:await (g r rw/ID) (mapv #(g (row-of %) rw/ID) ds) mode aid])
            (ek (cycle-ex x d)))
      ;; Fast path: settled members fill their slots in this commit.
      (let [remaining (volatile! n)
            winner (volatile! nil)]
        (dotimes [i n]
          (let [d (row-of (nth ds i))
                e (rv w (aget members i))]
            (when (and (nil? @winner) (or (nil? e) (settled? d)))
              (when e (s! e rw/E-SEEN (g d rw/VERSION)))
              (aset slots i (debtor-result d))
              (aset members i nil)
              (vswap! remaining dec)
              (when (= mode :any) (vreset! winner i)))))
        (if (or (zero? @remaining) (some? @winner))
          (do
            ;; complete at once: unfilled any-losers and final dep edges go
            (dotimes [i n]
              (when-let [e (rv w (aget members i))]
                (aset members i nil)
                (when (and (== rw/EK-WAIT (gl e rw/E-KIND)) (linked? w e)) (unlink! w e))))
            (when in-comp?
              (doseq [d ds] (let [d (row-of d)]
                              (when (final? d)
                                (let [ins (g x rw/C-INS)]
                                  (dotimes [i (acount ins)]
                                    (let [e (rv w (anth ins i))]
                                      (when (and (identical? d (rv w (g e rw/E-DEBTOR))) (== at (gl e rw/E-AT)))
                                        (remove-dep! w e)))))))))
            (commit! w [:await (g r rw/ID) (mapv #(g (row-of %) rw/ID) ds) mode [:opaque k] aid (mine-of w r ds)])
            (continue! (group-result mode slots @winner) k ek))
          (let [a (new-activation! w aid r mode k ek members slots @remaining)]
            (dotimes [i n]
              (when-let [e (rv w (aget members i))]
                (if (== rw/EK-DEP (gl e rw/E-KIND))
                  (s! e rw/E-ACT a)
                  (s! e rw/E-CRED a))))
            (park! r a)
            (commit! w [:await (g r rw/ID) (mapv #(g (row-of %) rw/ID) ds) mode [:opaque k] aid (mine-of w r ds)])
            (notify-blocked! x 0)
            ;; Demanded debtors run on the host stack (I10).
            (dotimes [i n]
              (when-not (act-done? a)
                (demand! w (row-of (nth ds i)))))
            (if (and (g a rw/A-RESUMED) (== rw/ACT-ACTIVE (gl r rw/R-ACT)) (run-current? w r))
              (do (s! r rw/R-SLICE true)
                  (set-active! r)
                  (commit! w [:schedule (g r rw/ID)])
                  (continue! (g a rw/A-RESULT) k ek))
              (do (s! a rw/A-INLINE false)
                  (when (g a rw/A-RESUMED) (aadd! (g w rw/W-RESUME) a))
                  nil))))))))))

(declare consume-effect!)

(defn- consuming?
  "A mailbox or a semaphore: read only by its consuming operation (Z#54)."
  [x]
  (and (source? x)
       (let [kind (gl x rw/X-KIND)] (or (== kind rw/SRC-MAILBOX) (== kind rw/SRC-SEMAPHORE)))))

(defn await-effect!
  "T6 with mode `one`; on a mailbox it is `take` (Z#54)."
  [d k ek]
  (if (consuming? d)
    (if (== rw/SRC-MAILBOX (gl d rw/X-KIND))
      (consume-effect! d k ek)
      (ek (invalid-op :await "await on a semaphore: use acquire!")))
    (await-group! [d] :one k ek)))

(defn- group-effect! [ds mode k ek]
  (let [ds (vec ds)]
    (if (some #(consuming? (row-of %)) ds)
      (ek (invalid-op mode "a group await cannot take from a mailbox or semaphore"))
      (await-group! ds mode k ek))))

(defn await-all-effect! [ds k ek] (group-effect! ds :all k ek))
(defn await-any-effect! [ds k ek] (group-effect! ds :any k ek))

(defn- same-capture?
  "Formalism §1.6: `identical?`, or for a scalar the same value of the same type."
  [a b]
  (or (identical? a b)
      #?(:clj (and (or (number? a) (char? a) (keyword? a) (symbol? a) (boolean? a) (string? a))
                   (.equals ^Object a b))
         :cljs (cond (number? a) (and (number? b) (.is js/Object a b))
                     (or (keyword? a) (symbol? a) (string? a)) (= a b)
                     :else false))))

(defn- same-inputs? [a b]
  (let [^objects a a ^objects b b]
    (and (== (alength a) (alength b))
         (loop [i 0]
           (or (== i (alength a))
               (and (same-capture? (aget a i) (aget b i)) (recur (inc i))))))))

;; A host handle (§1): weak, never a liveness reason. `cell` holds the row
;; (set when the creating item commits); `dropped` makes T19 happen once,
;; by `release!` or by the Cleaner after the handle is collected (M3c).
(deftype Handle [w ^objects cell dropped]
  #?@(:clj [clojure.lang.IDeref
            (deref [this] (value this))]))


(declare host! handle-drop! href)

(defn- new-handle
  "A fresh handle object for `w`; T19 is enqueued when it is collected. The
   cleaning action holds the cell and the flag, never the handle."
  [w row]
  (let [cell (object-array 1)
        dropped (hs/flag false)
        h (Handle. w cell dropped)]
    (aset cell 0 row)
    ;; T19 on collection matters only where the engine keeps rows that have no
    ;; engine reason: the verify registry. In production such rows are held by
    ;; their handles alone, so the host GC frees them with the handle, and no
    ;; Cleaner traffic competes for the gate (§1, G1).
    (when (some? (g w rw/W-REG))
      (hs/on-collect! h (fn []
                          (when (hs/flag-cas! dropped false true)
                            (host! w #(when-let [x (aget cell 0)] (handle-drop! w x)))))))
    h))

(defn- handle!
  "The row's live handle, or a new one (+1 handle, Z#29). A row has at most
   one live handle object."
  [w row]
  (or (let [r (g row rw/HREF)] (if (instance? Handle r) r (hs/deref-weak r)))
      (let [h (new-handle w row)
            again? (some? (g row rw/HREF))]
        (s! row rw/HANDLES (inc (gl row rw/HANDLES)))
        (s! row rw/HREF (href w h))
        (when again? (commit! w [:handle-new (g row rw/ID)]))
        h)))

(defn- href
  "How a row holds its live handle: weakly in verify mode, where collection
   drives T19 (Cleaner), strongly otherwise, where nothing depends on it and
   the host GC frees row and handle together."
  [w h]
  (if (some? (g w rw/W-REG)) (hs/weak h) h))

(defn- top-handle
  "A handle returned before its creating item commits (H1)."
  [w]
  (new-handle w nil))

(defn- bind-handle!
  "The creating item commits: the handle names its row, which holds it weakly."
  [h row]
  (aset ^objects (.-cell ^Handle h) 0 row)
  (s! row rw/HREF (href (.-w ^Handle h) h)))

(defn row-of
  "The row behind a handle, as the processed world sees it."
  [h] (let [w (cw)
            x (if (instance? Handle h) (aget ^objects (.-cell ^Handle h) 0) h)]
        (if w (rv w x) x)))

(defn- debtor-row [w type size owner key at handles]
  (let [x (rw/new-row (g w rw/W-EPOCH) size)]
    (s! x rw/TYPE type)
    (s! x rw/ID (alloc-id! w))
    (s! x rw/OUTS (alist))
    (s! x rw/REFS 0)
    (s! x rw/HOT 0)
    (s! x rw/HANDLES handles)
    (s! x rw/OWNER owner)
    (s! x rw/VERSION 0)
    (s! x rw/KEY key)
    (s! x rw/AT at)
    x))

(defn- new-comp! [w owner key at inputs body handles]
  (let [c (debtor-row w rw/T-COMP rw/C-SIZE owner key at handles)]
    (s! c rw/C-INPUTS inputs)
    (s! c rw/C-BODY body)
    (s! c rw/C-EPOCH 1)
    (s! c rw/C-PENDING 0)
    (s! c rw/C-RANK 0)
    (s! c rw/C-IDLE false)
    (s! c rw/C-INS (alist))
    (s! c rw/C-QUEUED false)
    (s! c rw/C-RESTART false)
    (register! w c)))

(defn- find-created [w l key]
  (when l
    (loop [i 0]
      (when (< i (acount l))
        (let [x (rv w (anth l i))]
          (if (== (long key) (gl x rw/KEY)) i (recur (inc i))))))))

(defn- creation-key! [r site]
  (let [ords (or (g r rw/R-ORD) (let [m (hs/vmap)] (s! r rw/R-ORD m) m))
        ord (long (or (hs/mget ords site) 0))]
    (hs/mput! ords site (inc ord))
    (+ (* (long site) 1048576) ord)))   ; site < 2^30, ord < 2^20: exact in JS doubles

(defn- adopt!
  "The creation of `c` with `key`, from its basis or its adoption basis."
  [w c key]
  (let [basis (or (g c rw/C-BASIS) (let [l (alist)] (s! c rw/C-BASIS l) l))
        bi (find-created w basis key)
        ab (g c rw/C-ADOPT)
        ai (when-not bi (find-created w ab key))]
    (cond bi (rv w (anth basis bi))
          ai (let [x (rv w (anth ab ai))]
               (aput! ab ai (rv w (anth ab (dec (acount ab))))) (apop! ab)
               (aadd! basis x)   ; the adoption reference moves to the basis
               x))))

(defn create-comp!
  "T3. `site` is a macro-time int, `inputs` the captured values."
  [site inputs body]
  (if-let [r (active-run)]
    (when (valid-run)
      (let [w (cw)
            c (rv w (g r rw/R-OF))
            at (next-at! r)]
        (if-not (comp? c)
          ;; Created by a task run: owned by the run scope, retained by demand.
          (let [child (new-comp! w (run-scope! w r) 0 at inputs body 0)]
            (aadd! (g w rw/W-RQ) child)
            (let [h (handle! w child)]
              (commit! w [:create-comp (g r rw/ID) (g child rw/ID) [:opaque-seq inputs] [:opaque body]])
              h))
          (let [key (creation-key! r site)
                child (adopt! w c key)]
            (if child
              (do (s! child rw/AT at)   ; adoption reuses the live handle, or makes one (Z#29)
                  (when (comp? child)
                    (when-not (same-inputs? inputs (g child rw/C-INPUTS))
                      ;; W#5: like a write to the rerun source.
                      (s! child rw/C-INPUTS inputs)
                      (s! child rw/C-BODY body)
                      (if (g child rw/C-IDLE)
                        (do (s! child rw/C-IDLE false) (s! child rw/C-VALIDITY nil)
                            (s! child rw/C-EPOCH (inc (gl child rw/C-EPOCH))))
                        (do (s! child rw/C-EPOCH (inc (gl child rw/C-EPOCH)))
                            (s! child rw/C-RESTART true)
                            (mark-from! w child)
                            (maybe-schedule! w child)))))
                  (let [h (handle! w child)]
                    (commit! w [:create-comp (g r rw/ID) (g child rw/ID) [:opaque-seq inputs] [:opaque body]])
                    h))
              ;; A body creation gets the body's weak handle (Z#13): +1 in handle!
              (let [child (new-comp! w c key at inputs body 0)]
                (aadd! (g c rw/C-BASIS) child)
                (ref-inc! child)
                (let [h (handle! w child)]
                  (commit! w [:create-comp (g r rw/ID) (g child rw/ID) [:opaque-seq inputs] [:opaque body]])
                  h)))))))
    (let [w (or *world* (throw (ex-info "no world: bind v2/*world*" {})))
          h (top-handle w)]
      (gated w
        (let [c (new-comp! w (rv w (g w rw/W-ROOT)) 0 0 inputs body 1)]
          (bind-handle! h c)
          (aadd! (g w rw/W-RQ) c)   ; outside live: Rule R makes it idle (§3.4)
          (commit! w [:create-comp-top (g (rv w (g w rw/W-ROOT)) rw/ID) (g c rw/ID) [:opaque-seq inputs] [:opaque body]])))
      h)))

(defn- new-task! [w owner key at inputs body handles]
  (let [k (debtor-row w rw/T-TASK rw/K-SIZE owner key at handles)]
    (s! k rw/K-BODY body)
    (s! k rw/K-INPUTS inputs)
    (s! k rw/K-DONE false)
    (register! w k)))

(defn- start-task! [w k]
  (let [r (new-run! w k 0)]
    (aadd! (g w rw/W-START) r)
    r))

(defn spawn!
  "T4. Inside a computation run the task is a creation in its basis,
   adopted by later runs (§5.2); inside a task run it is a structured child
   of the run scope (Q10); at top level it is owned by the root scope."
  [site inputs body]
  (if-let [r (active-run)]
    (when (valid-run)
      (let [w (cw)
            x (rv w (g r rw/R-OF))
            at (next-at! r)]
        (if (comp? x)
          (let [key (creation-key! r site)
                old (adopt! w x key)]
            (if (and old (task? old) (same-inputs? inputs (g old rw/K-INPUTS)))
              (do (s! old rw/AT at)
                  (let [h (handle! w old)]
                    (commit! w [:spawn (g r rw/ID) [:opaque body] (g old rw/ID) [:opaque-seq inputs]])
                    h))
              (do (when old                       ; changed captures: replace it
                    (let [basis (g x rw/C-BASIS)
                          i (idx-of basis old)]
                      (hs/remove-at! basis i)
                      (when-let [or* (rv w (g old rw/K-RUN))] (cancel! w or* ::cancelled))
                      (ref-dec! w old)))
                  (let [k (new-task! w x key at inputs body 0)]
                    (aadd! (g x rw/C-BASIS) k)
                    (ref-inc! k)
                    (start-task! w k)
                    (let [h (handle! w k)]
                      (commit! w [:spawn (g r rw/ID) [:opaque body] (g k rw/ID) [:opaque-seq inputs]])
                      h)))))
          (let [s (current-scope! w r)
                k (new-task! w s 0 at inputs body 0)]
            (hs/oset-add! (g s rw/S-TASKS) (id-of k) k)
            (ref-inc! k)
            (start-task! w k)
            (let [h (handle! w k)]
              (commit! w [:spawn (g r rw/ID) [:opaque body] (g k rw/ID) [:opaque-seq inputs]])
              h)))))
    (let [w (or *world* (throw (ex-info "no world: bind v2/*world*" {})))
          h (top-handle w)]
      (gated w
        (let [s (rv w (g w rw/W-ROOT))
              k (new-task! w s 0 0 inputs body 1)]
          (bind-handle! h k)
          (hs/oset-add! (g s rw/S-TASKS) (id-of k) k)
          (ref-inc! k)
          (start-task! w k)
          (commit! w [:spawn-top (g s rw/ID) [:opaque body] (g k rw/ID) [:opaque-seq inputs]])))
      h)))

;; ---------------------------------------------------------------------------
;; Idle validation (§3.4, R#3)

(defn- validate!
  "Idle `c` becomes live with restart edges when every debtor in its
   validity still has the recorded version (Z#24); otherwise it must run."
  [w c]
  (let [vs (g c rw/C-VALIDITY)
        ok? (and (not= :invalid vs)
                 (every? (fn [[d ver]]
                           (let [d (rv w d)]
                             (when (and (comp? d) (g d rw/C-IDLE)) (validate! w d))
                             (and (== (long ver) (gl d rw/VERSION))
                                  (or (source? d) (live? d)))))
                         vs))]
    (s! c rw/C-IDLE false)
    (s! c rw/C-VALIDITY nil)
    (if (and ok? (some? (g c rw/C-DONE-EPOCH)))
      (let [ins (g c rw/C-INS)]
        (doseq [[d ver at base] (when (sequential? vs) vs)]
          ;; Z#51: a final debtor whose version still matches keeps the value
          ;; valid but takes no edge (consumed, as T6/T10/Z#48)
          (let [d (rv w d)]
            (when-not (final? d)
              (let [e (link! w rw/EK-DEP c d at)]
                (s! e rw/E-SEEN ver)
                (s! e rw/E-BASE base)
                (aadd! ins e)))))
        (s! c rw/C-DONE-EPOCH (g c rw/C-EPOCH)))
      ;; B2: an invalid idle computation with a result steps its epoch so it
      ;; stays dirty while it runs; a fresh one needs no step.
      (when (some? (g c rw/C-DONE-EPOCH))
        (s! c rw/C-EPOCH (inc (gl c rw/C-EPOCH)))))
    ;; a demand that consumes the value without an edge (a task's fast path)
    ;; leaves it unreferenced: Rule R demotes it again (§3.3)
    (when (zero? (gl c rw/REFS)) (aadd! (g w rw/W-RQ) c))))

;; ---------------------------------------------------------------------------
;; Demand

(defn- demand!
  "Runs a demanded debtor that needs a run and is eligible (T6 demand)."
  [w d]
  (cond
    (comp? d)
    (do (when (g d rw/C-IDLE) (validate! w d))
        (when (and (needs-run? w d) (eligible? w d))
          (dispatch! w d)))
    (task? d) nil))

;; ---------------------------------------------------------------------------
;; Rule R (§3.3) by retention counts

(defn- demote!
  "§3.3 step 1.3: a computation outside `live`."
  [w c]
  (when-let [r (rv w (g c rw/C-RUN))]
    (cancel! w r ::cancelled)
    ;; a cancelled run that survives in cleanup must not count as current (I10)
    (when (current? c r) (s! c rw/C-EPOCH (inc (gl c rw/C-EPOCH)))))
  (let [ins (g c rw/C-INS)
        validity (loop [acc []]
                   (if (pos? (acount ins))
                     (let [e (rv w (apop! ins))
                           d (rv w (g e rw/E-DEBTOR))
                           acc (conj acc [d (g e rw/E-SEEN) (g e rw/E-AT) (g e rw/E-BASE)])]
                       (unlink! w e)
                       (recur acc))
                     acc))]
    (when-let [b (g c rw/C-BASIS)]
      (s! c rw/C-BASIS nil)
      (dotimes [i (acount b)]
        (let [x (rv w (anth b i))]
          (when (and (task? x) (rv w (g x rw/K-RUN))) (cancel! w (rv w (g x rw/K-RUN)) ::cancelled))
          (ref-dec! w x))))
    (release-adoption! w c)
    (s! c rw/C-PENDING 0)
    (if (or (some? (g c rw/C-DONE-EPOCH)) (pos? (gl c rw/HANDLES)))
      (do (s! c rw/C-IDLE true)
          (s! c rw/C-VALIDITY (when (some? (g c rw/C-DONE-EPOCH))
                                (if (every? (comp some? second) validity) validity :invalid))))
      (unregister! w c))))

(defn- rule-r!
  "Processes rows whose retention count reached 0."
  [w]
  (let [rq (g w rw/W-RQ)]
    (loop []
      (when (pos? (acount rq))
        (let [row (rv w (apop! rq))]
          (when (zero? (gl row rw/REFS))
            (cond
              (comp? row)
              (do (when-not (g row rw/C-IDLE) (demote! w row))
                  (when (and (g row rw/C-IDLE) (zero? (gl row rw/HANDLES)))
                    (unregister! w row)))
              (task? row)
              (when (and (g row rw/K-DONE) (zero? (gl row rw/HANDLES)))
                (unregister! w row))
              (source? row)
              (when (zero? (gl row rw/HANDLES)) (unregister! w row)))))
        (recur)))))

;; ---------------------------------------------------------------------------
;; Drain

(defn- resume-act! [w a]
  (let [r (rv w (g a rw/A-RUN))
        k (g a rw/A-R) ek (g a rw/A-E)]
    (cond
      ;; the resumed run gets its slice: a scheduling choice (D0)
      (and (== rw/ACT-ACTIVE (gl r rw/R-ACT)) (run-current? w r))
      (do (s! r rw/R-SLICE true)
          (commit! w [:schedule (g r rw/ID)])
          (slice! r #(continue! (g a rw/A-RESULT) k ek)))
      ;; cancelled between its resumption and its slice, with open finally
      ;; regions: it unwinds through the error continuation (T14)
      (and (== rw/ACT-DONE (gl r rw/R-ACT)) (pos? (fins r)) (not (g r rw/R-SLICE)))
      (do (s! r rw/R-SLICE true)
          (commit! w [:finalize (g r rw/ID)])
          (slice! r #(ek (cancelled-ex ::cancelled))))
      :else (retire-check! w r))))

(defn- start! [w r]
  (when (== rw/ACT-ACTIVE (gl r rw/R-ACT))
    (let [k (rv w (g r rw/R-OF))]
      (s! r rw/R-SLICE true)
      (commit! w [:schedule (g r rw/ID)])
      (slice! r #((g k rw/K-BODY) ok-k err-k)))))

(defn- pop-first! [w l]
  (let [x (rv w (anth l 0))]
    (hs/remove-first! l)
    x))

(defn- drain-step!
  "One unit of internal work (a cleanup slice, a task start, a resumption or
   a dispatch), then Rule R. False when there is none."
  [w]
  (let [ready (g w rw/W-READY)
        resume (g w rw/W-RESUME)
        start (g w rw/W-START)
        cleanup (g w rw/W-CLEANUP)]
    (cond
      (pos? (acount cleanup))
      (let [[r ek ex] (pop-first! w cleanup)]
        (s! r rw/R-SLICE true)
        (commit! w [:finalize (g r rw/ID)])
        (slice! r #(ek ex))
        (rule-r! w)
        true)
      (pos? (acount start)) (do (start! w (pop-first! w start)) (rule-r! w) true)
      (pos? (acount resume)) (do (resume-act! w (pop-first! w resume)) (rule-r! w) true)
      (pos? (acount ready))
      (let [c (pop-first! w ready)]
        (s! c rw/C-QUEUED false)
        (when (and (hot? c) (needs-run? w c) (eligible? w c))
          (dispatch! w c))
        (rule-r! w)
        true)
      :else false)))

(defn- run-callbacks!
  "Host callbacks run between items, on the processing thread (H3)."
  [w]
  (let [cbs (g w rw/W-CALLBACKS)]
    (when (pos? (acount cbs))
      (let [batch (acopy cbs)]
        (aclear! cbs)
        (dotimes [i (acount batch)]
          (let [[cb [v err?]] (rv w (anth batch i))] (cb v err?)))
        true))))

(defn- ingress [w] (g w rw/W-INGRESS))

(declare activate-dormant!)

(defn- run-turn!
  "H2: processes ingress items and internal work up to the budget. Returns
   true when work remains."
  [w]
  (s! w rw/W-DRAINING true)
  (when (or (g w rw/W-DORMANT) (g w rw/W-SP-DORMANT)) (activate-dormant! w))
  (try
    (loop [n (gl w rw/W-BUDGET)]
      (if (zero? n)
        true
        (if-let [item (hs/mpsc-poll! (ingress w))]
          (do (item) (recur (dec n)))
          (cond (drain-step! w) (recur (dec n))
                (run-callbacks! w) (recur n)
                :else false))))
    (finally (s! w rw/W-DRAINING false))))

(declare handoff! activate-dormant!)

(defn- process!
  "H2: try the gate; the winner runs a bounded turn, then hands off."
  [w]
  (let [lk (g w rw/W-LOCK)]
    (when (hs/try-lock! lk)
      (let [prev (enter-world! w)]
        (try (run-turn! w) (finally (hs/unlock! lk) (leave-world! prev)))))
    (handoff! w)))

(defn- work-pending? [w]
  (or (not (hs/mpsc-empty? (ingress w)))
      (pos? (acount (g w rw/W-READY))) (pos? (acount (g w rw/W-RESUME)))
      (pos? (acount (g w rw/W-START))) (pos? (acount (g w rw/W-CLEANUP)))
      (pos? (acount (g w rw/W-CALLBACKS)))))

(defn- handoff!
  "H2: after releasing the gate, queued work is never stranded: schedule the
   world's drainer when work remains and none is scheduled."
  [w]
  (let [sched (g w rw/W-SCHEDULED)]
    (when (and (work-pending? w) (hs/flag-cas! sched false true))
      (hs/execute! (g w rw/W-EXEC) (fn [] (hs/flag-set! sched false) (process! w))))))

(defn released-ex [] (ex-info "world released" {:spindel/released true}))

(defn host!
  "H1: a host operation `f` of world `w`. A thread that already holds the
   world (inside a slice or a callback) runs it at once; any other thread
   enqueues it, then tries the gate (H2) unless the world is not inline.
   A released world refuses host operations (T21)."
  [w f]
  (let [lk (g w rw/W-LOCK)]
    (cond
      (g w rw/W-RELEASED) (throw (released-ex))
      (hs/held? lk) (if (identical? w (cw))
                      (f)
                      (let [prev (enter-world! w)] (try (f) (finally (leave-world! prev)))))
      ;; Fast path: nothing queued and the gate is free, so running the item
      ;; now keeps FIFO order without an ingress node.
      (and (g w rw/W-INLINE) (hs/mpsc-empty? (ingress w)) (hs/try-lock! lk))
      (let [prev (enter-world! w)
            v (try (s! w rw/W-DRAINING true)
                   (let [v (try (f) (finally (s! w rw/W-DRAINING false)))]
                     (run-turn! w)
                     v)
                   (finally (hs/unlock! lk) (leave-world! prev)))]
        (handoff! w)
        v)
      :else
      (do (hs/mpsc-add! (ingress w) f)
          (if (g w rw/W-INLINE) (process! w) (handoff! w))
          nil))))

(defn- world-of
  "The world a host operation on `h` acts on. Inside a slice it is the
   slice's world (Z#44: such operations are effects of the running run, and
   a body copied into a fork addresses the fork); outside, the handle's."
  [h]
  (if (and (active-run) (cw))
    (cw)
    (if (instance? Handle h) (.-w ^Handle h) (cw))))

;; ---------------------------------------------------------------------------
;; Host API

(defn- new-source! [w kind v owner key at]
  (let [x (debtor-row w rw/T-SOURCE rw/X-SIZE owner key at 1)]
    (s! x rw/X-KIND kind)
    (s! x rw/X-VALUE v)
    (s! x rw/X-OPEN true)
    (register! w x)))

(defn- own-source!
  "Records a source owned by scope `sc`, weakly: the scope closes it if it
   still exists (T16), but never keeps it alive (§5.2, G1). Dead entries are
   pruned when the list doubles."
  [w sc x]
  (let [l (or (g sc rw/S-SOURCES) (let [l (alist)] (s! sc rw/S-SOURCES l) (s! sc rw/S-PRUNE 8) l))]
    (aadd! l (hs/weak x))
    (when (> (acount l) (gl sc rw/S-PRUNE))
      (let [live (alist)]
        (dotimes [i (acount l)]
          (let [r (rv w (anth l i))] (when (hs/deref-weak r) (aadd! live r))))
        (s! sc rw/S-SOURCES live)
        (s! sc rw/S-PRUNE (max 8 (* 2 (acount live))))))))

(defn- close-source!
  "A closed source is final and read-only (T16, R#15): its dep edges are
   removed after their current delivery (T10)."
  [w x]
  (when (g x rw/X-OPEN)
    (s! x rw/X-OPEN false)
    (settle! w x)))

(defn- create-source-in-run!
  "T1 inside a run: owned by the computation (in its basis, adopted by later
   runs in creation order) or by the task run's current scope, which retains
   it only through edges and handles (§5.2)."
  [r kind v init]
  (let [w (cw)
        x (rv w (g r rw/R-OF))
        at (next-at! r)]
    (if (comp? x)
      (let [key (creation-key! r -1)
            old (adopt! w x key)]
        (if (and old (source? old))
          (do (s! old rw/AT at)
              (let [h (handle! w old)]
                (commit! w [:create-source (g r rw/ID) ([:signal :cell :deferred :mailbox :semaphore] kind)
                            [:opaque (when-not (== kind rw/SRC-MAILBOX) v)] (g old rw/ID)])
                h))
          (let [s (new-source! w kind v x key at)]
            (s! s rw/HANDLES 0)
            (when init (init s))
            (aadd! (g x rw/C-BASIS) s)
            (ref-inc! s)
            (let [h (handle! w s)]
              (commit! w [:create-source (g r rw/ID) ([:signal :cell :deferred :mailbox :semaphore] kind)
                          [:opaque (when-not (== kind rw/SRC-MAILBOX) v)] (g s rw/ID)])
              h))))
      (let [sc (current-scope! w r)
            s (new-source! w kind v sc 0 at)]
        (own-source! w sc s)
        (s! s rw/HANDLES 0)
        (when init (init s))
        (aadd! (g w rw/W-RQ) s)
        (let [h (handle! w s)]
          (commit! w [:create-source (g r rw/ID) ([:signal :cell :deferred :mailbox :semaphore] kind)
                      [:opaque (when-not (== kind rw/SRC-MAILBOX) v)] (g s rw/ID)])
          h)))))

(defn- create-source-top! [w kind v init]
  (if-let [r (active-run)]
    (if (valid-run) (create-source-in-run! r kind v init) (throw (ex-info "source creation in a cancelled run" {})))
    (create-source-top-host! w kind v init)))

(defn- create-source-top-host! [w kind v init]
  (let [h (top-handle w)]
    (gated w
      (let [x (new-source! w kind v (rv w (g w rw/W-ROOT)) 0 0)]
        (when init (init x))
        (bind-handle! h x)
        (commit! w [:create-source-top (g (rv w (g w rw/W-ROOT)) rw/ID)
                    ([:signal :cell :deferred :mailbox :semaphore] kind)
                    [:opaque (when-not (== kind rw/SRC-MAILBOX) v)] (g x rw/ID)])))
    h))

(defn signal
  "T1 at top level: a signal in `w` (default `*world*`)."
  ([v] (signal *world* v))
  ([w v] (create-source-top! w rw/SRC-SIGNAL v nil)))

(defn- mailbox? [x] (== rw/SRC-MAILBOX (gl x rw/X-KIND)))

(defn- deque [x i] (g x i))

(defn- available? [x]
  (if (mailbox? x)
    (not (hs/dq-empty? (deque x rw/X-VALUE)))
    (pos? (gl x rw/X-VALUE))))

(defn- consume! [x]
  (if (mailbox? x)
    (hs/dq-poll! (deque x rw/X-VALUE))
    (do (s! x rw/X-VALUE (dec (gl x rw/X-VALUE))) true)))

(defn consume-effect!
  "`take!` (mailbox) or `acquire!` (semaphore): a consuming operation, always
   a wait edge, never a dependency (§4.3). Waiters are served FIFO."
  [x k ek]
  (if-let [r (valid-run)]
    (let [w (cw)
          at (next-at! r)
          aid (alloc-id! w)]
      (if (available? x)
        (let [v (consume! x)]
          (alloc-id! w)                             ; the consumed wait edge
          (s! x rw/VERSION (inc (gl x rw/VERSION)))
          (commit! w [:take (g r rw/ID) (g x rw/ID) aid])
          (k v))
        (let [members (object-array 1)
              a (new-activation! w aid r :one k ek members (object-array 1) 1)
              e (link! w rw/EK-WAIT a x at)]
          (aset members 0 e)
          (hs/dq-push! (deque x rw/X-WAITERS) e)
          (park! r a)
          (s! a rw/A-INLINE false)
          (commit! w [:take (g r rw/ID) (g x rw/ID) aid])
          (notify-blocked! (rv w (g r rw/R-OF)) 0)
          nil)))
    (unwind! ek)))

(defn- serve-waiter!
  "The first waiter whose activation can still receive gets `v`. Waiters of
   stale or cancelled runs are skipped (§4.5.4)."
  [w x v]
  (let [q (deque x rw/X-WAITERS)]
    (loop []
      (when-let [e (hs/dq-poll! q)]
        (let [a (rv w (g e rw/E-CRED))
              r (rv w (g a rw/A-RUN))]
          (if (and (linked? w e) (identical? a (rv w (g r rw/R-ACTV))) (run-current? w r)
                   (== rw/ACT-PARKED (gl r rw/R-ACT)))
            (do (unlink! w e)
                (slot-fill! w a e [v false])
                true)
            (recur)))))))

(defn mailbox
  "T1 at top level: a FIFO mailbox (§4.3)."
  ([] (mailbox *world*))
  ([w] (create-source-top! w rw/SRC-MAILBOX (hs/deque)
                           #(s! % rw/X-WAITERS (hs/deque)))))

(defn post!
  "Appends `v`, or hands it to the first waiter, atomically (§4.3)."
  [h v]
  (gated (world-of h)
    (let [x (row-of h) w (cw)]
      (if (closed? x)
        (refuse! w [:post (g x rw/ID) [:opaque v]])
        (do (s! x rw/VERSION (inc (gl x rw/VERSION)))
            (when-not (serve-waiter! w x v)
              (hs/dq-push! (deque x rw/X-VALUE) v))
            (commit! w [:post (g x rw/ID) [:opaque v]])))))
  nil)

(defn semaphore
  "T1 at top level: a counting semaphore with `n` permits (§4.3)."
  ([n] (semaphore *world* n))
  ([w n] (create-source-top! w rw/SRC-SEMAPHORE (long n)
                             #(s! % rw/X-WAITERS (hs/deque)))))

(defn sem-release!
  "Gives the permit to the first armed waiter, or returns it (§4.3)."
  [h]
  (gated (world-of h)
    (let [x (row-of h) w (cw)]
      (if (closed? x)
        (refuse! w [:release (g x rw/ID)])
        (do (s! x rw/VERSION (inc (gl x rw/VERSION)))
            (when-not (serve-waiter! w x true)
              (s! x rw/X-VALUE (inc (gl x rw/X-VALUE))))
            (commit! w [:release (g x rw/ID)])))))
  nil)

(defn deferred
  "T1 at top level: a deferred, delivered once (§4.3)."
  ([] (deferred *world*))
  ([w] (create-source-top! w rw/SRC-DEFERRED nil nil)))

(defn deliver!
  "Delivers a deferred once: fires its edges and finalizes it (§4.3, T10).
   A second delivery is refused."
  [h v]
  (gated (world-of h)
    (let [x (row-of h) w (cw)]
      (if (final? x)
        (refuse! w [:deliver (g x rw/ID) [:opaque v]])
        (do (s! x rw/X-VALUE v)
            (s! x rw/VERSION 1)
            (settle! w x)
            (commit! w [:deliver (g x rw/ID) [:opaque v]])))))
  v)

(defn write!
  "T2: `version += 1`, fire dep edges and deliver observe edges (§4.5.1)."
  [h v]
  (gated (world-of h)
    (let [x (row-of h) w (cw)]
      (if (closed? x)
        (refuse! w [:write (g x rw/ID) [:opaque v]])
        (do
      (s! x rw/X-VALUE v)
      (s! x rw/VERSION (inc (gl x rw/VERSION)))
      (let [outs (acopy (g x rw/OUTS))]
        (dotimes [i (acount outs)]
          (let [e (rv w (anth outs i)) k (gl e rw/E-KIND)]
            (cond (== k rw/EK-DEP) (fire-dep! w e)
                  (== k rw/EK-OBSERVE) (deliver-observe! w e)))))
      (commit! w [:write (g x rw/ID) [:opaque v]])))))
  v)

(defn observe!
  "T8: `cb` receives (value err?) on each change. Returns an unobserve fn."
  [h cb]
  (let [w (world-of h)
        ev (volatile! nil)]
    (gated w
      (let [d (row-of h)
            e (link! w rw/EK-OBSERVE cb d 0)]
        (vreset! ev e)
        (when (and (comp? d) (g d rw/C-IDLE)) (validate! w d))
        (deliver-observe! w e)
        (commit! w [:observe (g d rw/ID) [:opaque cb] (g e rw/ID)])
        (demand! w d)))
    (fn []
      (gated w
        (when-let [e @ev]
          (when (linked? w e)
            (unlink! w e)
            (commit! w [:unobserve (g e rw/ID)]))))
      nil)))

(defn pin!
  "T20: a row is a root while its pin count is positive (Z#16)."
  [h]
  (gated (world-of h)
    (let [x (row-of h) w (cw)
          pins (g w rw/W-PINS)
          n (long (or (second (hs/mget pins (id-of x))) 0))]
      (hs/mput! pins (id-of x) [x (inc n)])
      (ref-inc! x)
      (commit! w [:pin (g x rw/ID)])))
  h)

(defn unpin! [h]
  (gated (world-of h)
    (let [x (row-of h) w (cw)
          pins (g w rw/W-PINS)
          n (long (or (second (hs/mget pins (id-of x))) 0))]
      (if (zero? n)
        (refuse! w [:unpin (g x rw/ID)])
        (do (if (== n 1) (hs/mdel! pins (id-of x)) (hs/mput! pins (id-of x) [x (dec n)]))
            (ref-dec! w x)
            (commit! w [:unpin (g x rw/ID)])))))
  h)

(defn- handle-drop!
  "T19: `handles -= 1`; Rule R applies §3.4."
  [w x]
  (if (zero? (gl x rw/HANDLES))
    (refuse! w [:handle-drop (g x rw/ID)])
    (do (s! x rw/HANDLES (dec (gl x rw/HANDLES)))
        (when (zero? (gl x rw/REFS)) (aadd! (g w rw/W-RQ) x))
        (commit! w [:handle-drop (g x rw/ID)]))))

(defn release!
  "T19 by hand: drops this handle now instead of at collection."
  [h]
  (when (instance? Handle h)
    (let [^Handle h h
          dropped (.-dropped h)]
      (when (hs/flag-cas! dropped false true)
        (let [w (.-w h)]
          (gated w (when-let [x (row-of h)] (handle-drop! w x)))))))
  nil)

(defn cancel-task!
  "T14 from the host on a task."
  [h]
  (gated (world-of h)
    (let [k (row-of h) w (cw)]
      (if-let [r (let [r (rv w (g k rw/K-RUN))] (when (and r (not (g r rw/R-SLICE))) r))]
        (do (cancel! w r ::cancelled)
            (commit! w [:cancel (g r rw/ID)]))
        (refuse! w [:cancel (g k rw/ID)]))))
  nil)

(defn call-in!
  "Runs `(f)` as a host item of `w` and returns its value (JVM, blocking;
   tooling and tests). Inside the world it runs at once."
  [w f]
  #?(:clj (let [p (promise)]
            (host! w #(deliver p (try [(f) nil] (catch Throwable t [nil t]))))
            (let [[v t] @p] (if t (throw t) v)))
     :cljs (f)))

(defn value-async
  "T22/H3: demands `h` through a host wait edge and calls `(cb v err?)` once
   it settles. Returns a fn that withdraws the wait (host-unawait)."
  [h cb]
  (let [w (world-of h)
        ev (volatile! nil)]
    (gated w
      (let [d (row-of h)]
        (cond
          (consuming? d)
          (aadd! (g w rw/W-CALLBACKS) [cb [(invalid-op :value "a host read of a mailbox or semaphore (Z#54)") true]])
          (and (source? d) (not (deferred? d)))
          (aadd! (g w rw/W-CALLBACKS) [cb (debtor-result d)])
          :else
          ;; T22 allocates the host-wait edge first (the model's order); a
          ;; debtor that is settled consumes it at once, so no edge row is made.
          (let [eid (alloc-id! w)
                idle? (and (comp? d) (g d rw/C-IDLE))]
            (if (and (not idle?) (settled? d))
              (do (aadd! (g w rw/W-CALLBACKS) [cb (debtor-result d)])
                  (commit! w [:host-await (g d rw/ID) eid]))
              (let [e (link-id! w eid rw/EK-WAIT cb d 0)]
                (vreset! ev e)
                (when idle? (validate! w d))
                (if (settled? d)
                  (do (fire-wait! w e)
                      (commit! w [:host-await (g d rw/ID) (g e rw/ID)]))
                  (do (commit! w [:host-await (g d rw/ID) (g e rw/ID)])
                      (demand! w d)))))))))
    (fn []
      (gated w
        (when-let [e @ev]
          (when (linked? w e)
            (unlink! w e)
            (commit! w [:host-unawait (g e rw/ID)]))))
      nil)))

(defn value
  "Host read (H3): blocks the calling host thread on a host promise, outside
   the gate. Never call it inside a body (B7). With a timeout, returns
   `timeout-val` when the result is not there in time."
  ([h] (value h nil nil))
  ([h timeout-ms timeout-val]
   (when (active-run) (throw (ex-info "blocking value inside a body (B7)" {})))
   #?(:clj
      (let [p (promise)
            unawait (value-async h (fn [v err?] (deliver p [v err?])))
            res (if timeout-ms (deref p timeout-ms ::timeout) @p)]
        (if (= ::timeout res)
          (do (unawait) timeout-val)
          (let [[v err?] res] (if err? (throw v) v))))
      :cljs (throw (ex-info "blocking value is JVM-only; use value-async" {})))))

;; ---------------------------------------------------------------------------
;; Resources (T15, T17, T18): offload and timers


(defn- armed-set [w]
  (or (g w rw/W-ARMED) (let [s (hs/oset)] (s! w rw/W-ARMED s) s)))

(defn forked-ex [] (ex-info "forked" {:spindel/forked true}))

(declare join! cancel-resource! resource-fire! resource-ack!)

(declare sp-deliver!)

(defn- activate-dormant!
  "§8.1: a fork's inherited armed resources, at its first turn. A timer
   re-arms for its remaining time; any other resource (offload, external
   wait) never had a physical counterpart here: it fires err ::forked into
   its edges and joins at once."
  [w]
  ;; S3/§8.1: pending savepoints a fork inherited, other than its pending
  ;; activation, fail with err ::forked (the child has no publication for them)
  (when-let [as (g w rw/W-SP-DORMANT)]
    (s! w rw/W-SP-DORMANT nil)
    (let [pending (g w rw/W-PENDING-ACT)]
      (doseq [a0 as]
        (when-not (and pending (== (id-of a0) (long pending)))
          (let [a (rv w a0) r (rv w (g a rw/A-RUN))]
            (when (and (identical? a (rv w (g r rw/R-ACTV))) (== rw/ACT-PARKED (gl r rw/R-ACT)))
              (sp-deliver! w a [(forked-ex) true])))))))
  (when-let [zs (g w rw/W-DORMANT)]
    (s! w rw/W-DORMANT nil)
    (doseq [z0 zs]
      (let [z (rv w z0)]
        (when (== rw/Z-ARMED (gl z rw/Z-PHASE))
          (if (and (= :timer (g z rw/Z-KIND)) (g z rw/Z-DEADLINE))
            (let [left (max 0 (- (long (g z rw/Z-DEADLINE)) (hs/now-ms)))]
              (hs/oset-add! (armed-set w) (id-of z) z)
              (s! z rw/Z-CTL (hs/schedule! left (fn [] (join! w z [nil false])))))
            (do (resource-fire! w z [(forked-ex) true])
                (resource-ack! w z))))))))

(defn- new-resource!
  "T17: an outstanding resource owned by `r`, with `at = R.effect-index`."
  [w r kind at]
  (let [z (debtor-row w rw/T-RES rw/Z-SIZE r 0 at 0)]
    (s! z rw/Z-KIND kind)
    (s! z rw/Z-PHASE rw/Z-ARMED)
    (hs/oset-add! (armed-set w) (id-of z) z)
    (aadd! (or (g r rw/R-RES) (let [l (alist)] (s! r rw/R-RES l) l)) z)
    (register! w z)))

(defn- resource-fire!
  "T18: an armed resource fires once; its wait edges fire (Z#6)."
  [w z res]
  (if (== rw/Z-ARMED (gl z rw/Z-PHASE))
    (let [[v err?] res]
      (s! z rw/Z-PHASE rw/Z-FIRED)
      (hs/oset-del! (armed-set w) (id-of z))
      (s! z rw/Z-RESULT v)
      (s! z rw/Z-ERR (boolean err?))
      (let [outs (acopy (g z rw/OUTS))]
        (dotimes [i (acount outs)] (fire-wait! w (rv w (anth outs i)))))
      (commit! w [:resource-fire (g z rw/ID) (if err? 2 1) [:opaque v]]))
    (refuse! w [:resource-fire (g z rw/ID)])))

(defn- resource-ack!
  "T15: the resource has joined; its run may retire (T13)."
  [w z]
  (if (pos? (acount (g z rw/OUTS)))
    (refuse! w [:resource-ack (g z rw/ID)])
    (let [r (rv w (g z rw/OWNER))
          zs (g r rw/R-RES)
          i (idx-of zs z)]
      (when-not (neg? i)
        (hs/remove-at! zs i)
        (when (zero? (acount zs)) (s! r rw/R-RES nil))
        (unregister! w z)
        (commit! w [:resource-ack (g z rw/ID)])
        (retire-check! w r)))))

(defn- cancel-resource!
  "T14: an armed resource is told to cancel. One that provably never started
   (or whose timer was unscheduled) joins at once; a running offload is
   interrupted and joins when its function returns."
  [w z]
  (when (== rw/Z-ARMED (gl z rw/Z-PHASE))
    (s! z rw/Z-PHASE rw/Z-CANCELLING)
    (hs/oset-del! (armed-set w) (id-of z))
    (let [ctl (g z rw/Z-CTL)
          joined? (if (hs/timer? ctl) (hs/unschedule! ctl) (hs/ctl-cancel! ctl))]
      (when joined? (resource-ack! w z)))))

(defn- arm-and-park!
  "T17 then T6 on the new resource: the run waits for its fire."
  [r kind k ek start!]
  (let [w (cw)
        at (next-at! r)
        z (new-resource! w r kind at)
        _ (commit! w [:arm (g r rw/ID) kind (g z rw/ID)])
        aid (alloc-id! w)
        members (object-array 1)
        a (new-activation! w aid r :one k ek members (object-array 1) 1)
        e (link! w rw/EK-WAIT a z at)]
    (aset members 0 e)
    (park! r a)
    (s! a rw/A-INLINE false)
    (commit! w [:await (g r rw/ID) [(g z rw/ID)] :one [:opaque k] aid []])
    (notify-blocked! (rv w (g r rw/R-OF)) 0)
    (start! w z)
    nil))


(defn- join! [w z res]
  ;; the callback captured the row before any later fork: resolve it in `w`
  (host! w #(let [z (rv w z)] (resource-fire! w z res) (resource-ack! w z))))

(defn offload-effect!
  "`(offload f)`: runs the plain function `f` on the world's executor,
   outside every world (§4.3). `f` must not call into the world
   synchronously; it may enqueue ingress."
  [f k ek]
  (if-let [r (valid-run)]
    (arm-and-park!
     r :offload k ek
     (fn [w z]
       (let [ctl (hs/offload-ctl)]
         (s! z rw/Z-CTL ctl)
         (hs/execute! (g w rw/W-EXEC)
                      (fn []
                        (when (hs/ctl-start! ctl)
                          (let [res (try [(f) false] (catch #?(:clj Throwable :cljs :default) t [t true]))]
                            (hs/ctl-finish! ctl)
                            (join! w z res))))))))
    (unwind! ek)))

(defn sleep-effect!
  "`(sleep ms)`: a timer resource."
  [ms k ek]
  (if-let [r (valid-run)]
    (arm-and-park!
     r :timer k ek
     (fn [w z]
       (s! z rw/Z-DEADLINE (+ (hs/now-ms) (long ms)))
       (s! z rw/Z-CTL (hs/schedule! ms (fn [] (join! w z [nil false]))))))
    (unwind! ek)))

(defn release-world!
  "T21: revokes the roots (observe callbacks and host waits receive
   ::released, pins are dropped), closes the root scope, and lets Rule R
   reclaim the rest. Later host operations fail with ::released. Returns a
   fn reporting the rows left (cleanup entries until they retire, L2)."
  [w]
  (gated w
    (let [ex (released-ex)
          roots (g w rw/W-ROOTS)]
      (doseq [e (map #(rv w %) (hs/mvals roots))]
        (when (linked? w e)
          (let [cb (rv w (g e rw/E-CRED))]
            (unlink! w e)
            (aadd! (g w rw/W-CALLBACKS) [cb [ex true]]))))
      (let [pins (g w rw/W-PINS)]
        (doseq [[x n] (hs/mvals pins)] (dotimes [_ n] (ref-dec! w (rv w x))))
        (hs/mclear! pins))
      (close-scope! w (rv w (g w rw/W-ROOT)))
      ;; host admissions are revoked: released handles hold no row (T21)
      (when-let [reg (g w rw/W-REG)]
        (doseq [x (hs/mvals reg)]
          (when (and (#{rw/T-COMP rw/T-TASK rw/T-SOURCE} (gl x rw/TYPE)) (pos? (gl x rw/HANDLES)))
            (s! x rw/HANDLES 0)
            (when (zero? (gl x rw/REFS)) (aadd! (g w rw/W-RQ) x)))))
      (commit! w [:release-world])
      (s! w rw/W-RELEASED true)))
  (fn [] (when-let [reg (g w rw/W-REG)] (hs/msize reg))))

(defn open-scope!
  "T16 open: an explicit scope, child of the run's current scope, a root
   while open (§3.1). Used by `with-scope`."
  []
  (let [r (or (active-run) (throw (ex-info "with-scope outside a body" {})))
        w (cw)
        s (new-scope w (alloc-id! w) :explicit (current-scope! w r))]
    (aadd! (or (g r rw/R-SCOPES) (let [l (alist)] (s! r rw/R-SCOPES l) l)) s)
    (commit! w [:open-scope (g r rw/ID) (g s rw/ID)])
    s))

(defn close-scope-fx!
  "T16 close at the end of `with-scope`: cancels the work it still owns."
  [s]
  (let [w (cw)]
    (when-let [r (active-run)]
      (when-let [ss (g r rw/R-SCOPES)]
        (let [i (last-idx-of ss s)]
          (when-not (neg? i) (hs/remove-at! ss i)))))
    (close-scope! w s)
    (commit! w [:close-scope (g s rw/ID)])
    nil))

(defn detach!
  "Q10: re-owns a running task to an outer scope `s` (an explicit scope, or
   the world's root with `(root-scope w)`), so it outlives its creator."
  [h s]
  (let [w (world-of h)]
    (gated w
      (let [k (row-of h)
            old (rv w (g k rw/OWNER))]
        (if (or (g k rw/K-DONE) (not (g s rw/S-OPEN))
                (not (and old (not (fn? old)) (== rw/T-SCOPE (gl old rw/TYPE)))))
          (refuse! w [:detach (g k rw/ID) (g s rw/ID)])
          (do
            (hs/oset-del! (g old rw/S-TASKS) (id-of k))
            (hs/oset-add! (g s rw/S-TASKS) (id-of k) k)
            ;; the run scope's parent follows the owner (Z#26)
            (when-let [rs (when-let [kr (rv w (g k rw/K-RUN))] (rv w (g kr rw/R-SROW)))]
              (remove-row! (g old rw/S-CHILDREN) rs)
              (s! rs rw/S-PARENT s)
              (aadd! (g s rw/S-CHILDREN) rs))
            (s! k rw/OWNER s)
            (remove-scope-if-empty! w old)
            (commit! w [:detach (g k rw/ID) (g s rw/ID)])))))
    h))

(defn root-scope [w] (g w rw/W-ROOT))

(defn in-world
  "A handle naming the same row as `h`, in world `w` (e.g. a fork). The row
   resolves to `w`'s copy when `w` processes it."
  [w h]
  (new-handle w (aget ^objects (.-cell ^Handle h) 0)))

(defn- fork-world*
  "D3: the frozen copy-on-write fork of `w`, at the current commit. O(1) in
   the world's rows: both worlds get fresh epochs, so every existing row is a
   shared basis that each world copies on first access; the forward map (row
   ID -> copy) is shared persistently. The child gets fresh administration
   and copies of the queues, pins and roots (work in flight, design v3 §6);
   its inherited armed resources are dormant until its first turn (§8.1)."
  [w]
  (let [c (aclone ^objects w)
        armed (g w rw/W-ARMED)]
    (s! w rw/W-EPOCH #?(:clj (Object.) :cljs (js-obj)))
    (s! c rw/W-EPOCH #?(:clj (Object.) :cljs (js-obj)))
    (s! c rw/ID (alloc-id! w))
    (s! c rw/W-LOCK (hs/lock))
    (s! c rw/W-INGRESS (hs/mpsc))
    (s! c rw/W-SCHEDULED (hs/flag false))
    (s! c rw/W-DRAINING false)
    (s! c rw/W-CALLBACKS (alist))
    (doseq [i [rw/W-READY rw/W-RESUME rw/W-START rw/W-CLEANUP rw/W-RQ]]
      (s! c i (hs/lcopy (g w i))))
    (s! c rw/W-PINS (hs/mcopy (g w rw/W-PINS)))
    (s! c rw/W-ROOTS (hs/mcopy (g w rw/W-ROOTS)))
    (s! c rw/W-ARMED nil)
    ;; dormant: this world's armed resources and pending savepoints, plus what
    ;; it still holds dormant itself (a basis is never run, only forked)
    (s! c rw/W-DORMANT (seq (concat (when armed (hs/oset-vals armed)) (g w rw/W-DORMANT))))
    (let [sps (g w rw/W-SAVEPOINTS)]
      (s! c rw/W-SAVEPOINTS nil)
      (s! c rw/W-PENDING-ACT nil)
      (s! c rw/W-SP-DORMANT (seq (concat (when sps (hs/oset-vals sps)) (g w rw/W-SP-DORMANT)))))
    (when-let [reg (g w rw/W-REG)]
      (s! c rw/W-REG (hs/mcopy reg))
      (s! c rw/W-LOG (alist)))
    c))

(defn fork!
  "D3, host form: a frozen fork of `w` between slices. Returns the child
   world; act on it through `in-world` handles."
  [w]
  (let [res (volatile! nil)]
    (gated w
      (when (active-run) (throw (ex-info "fork! inside a body: use the (fork) effect" {})))
      (let [c (fork-world* w)]
        (commit! w [:fork-host (g c rw/ID)])
        (vreset! res c)))
    (handoff! @res)
    @res))

(defn fork-effect!
  "D3/Q4 `(fork)` in a task body: the fork boundary is this effect's commit.
   The parent continues with [:parent child-world]; in the child the run
   exists parked at the effect and resumes with [:child nil] (Q4)."
  [k ek]
  (if-let [r (valid-run)]
    (cond
      (comp? (rv (cw) (g r rw/R-OF)))
      (ek (ex-info "fork in a computation body is not supported" {}))
      (> (long (or (aget (ctx) 2) 0)) 1)
      (ek (ex-info "fork in a nested slice is not supported yet" {}))
      :else
      (let [w (cw)
            aid (alloc-id! w)
            a (new-activation! w aid r :one k ek (object-array 1) (object-array 1) 0)]
        ;; the child's view: the run resumed at the effect with its delivery
        (s! a rw/A-RESULT [[:child nil] false])
        (s! a rw/A-RESUMED true)
        (s! a rw/A-INLINE false)
        (s! r rw/R-SLICE false)
        (aadd! (g w rw/W-RESUME) a)
        (unregister! w a)                 ; a delivery carrier, not a parked activation
        (let [child (fork-world* w)]
          ;; the parent takes the delivery back and continues on its own copy
          (remove-row! (g w rw/W-RESUME) a)
          (let [r (rv w r)]
            (s! r rw/R-SLICE true)
            (set-active! r)
            (commit! w [:fork (g r rw/ID) (g child rw/ID)])
            (handoff! child)
            (k [:parent child])))))
    (unwind! ek)))

(defn fork [] (throw (ex-info "fork outside a body" {})))

;; ---------------------------------------------------------------------------
;; Savepoints (§8.2, S1-S7)

(defn install-handlers!
  "Merges `table` ({site handler}) into `w`'s savepoint handlers; a handler is
   called with the publication after the publishing commit (H3). `:default`
   matches every site without its own entry."
  [w table]
  (s! w rw/W-SP-HANDLERS (merge (g w rw/W-SP-HANDLERS) table))
  w)

(defn- sp-deliver!
  "Resumes the run parked on savepoint activation `a` with `res` (T9's
   savepoint branch): the activation goes, the run becomes active and its
   slice is scheduled. Only a run still parked on `a` resumes; false
   otherwise (it was cancelled meanwhile)."
  [w a res]
  (let [r (rv w (g a rw/A-RUN))]
    (if (and (== rw/ACT-PARKED (gl r rw/R-ACT))
             (some-> (rv w (g r rw/R-ACTV)) (identical? a)))
      (do (when-let [sps (g w rw/W-SAVEPOINTS)] (hs/oset-del! sps (id-of a)))
          (s! r rw/R-ACTV nil)
          (s! r rw/R-ACT rw/ACT-ACTIVE)
          (s! a rw/A-RESULT res)
          (s! a rw/A-RESUMED true)
          (unregister! w a)                  ; resumed: a delivery carrier now
          (aadd! (g w rw/W-RESUME) a)
          true)
      false)))

(defn savepoint-effect!
  "S1 `(savepoint site payload)`: with a handler for `site`, the run parks
   and a publication is offered to it, holding a frozen basis of the world at
   this commit; without one the effect is the identity on `payload`."
  [site payload k ek]
  (if-let [r (valid-run)]
    (let [w (cw)
          handlers (g w rw/W-SP-HANDLERS)
          h (or (get handlers site) (get handlers :default))]
      (cond
        (nil? h) (k payload)
        (comp? (rv w (g r rw/R-OF))) (ek (ex-info "savepoint in a computation body is not supported" {}))
        (> (long (or (aget (ctx) 2) 0)) 1) (ek (ex-info "savepoint in a nested slice is not supported yet" {}))
        :else
        (let [aid (alloc-id! w)
              a (new-activation! w aid r :one k ek (object-array 1) (object-array 1) 1)]
          (s! a rw/A-INLINE false)
          (park! r a)
          (hs/oset-add! (or (g w rw/W-SAVEPOINTS) (let [s (hs/oset)] (s! w rw/W-SAVEPOINTS s) s)) aid a)
          (commit! w [:savepoint (g r rw/ID) [:opaque site] [:opaque payload] aid])
          ;; the basis is a fork of this commit that is never run, only forked
          (let [basis (fork-world* w)
                pub {:world w :act aid :site site :payload payload :basis basis
                     :state (atom :pending)}]
            ;; the parent's own copy of the run keeps no slice (it is parked)
            (set-active! (rv w r))
            (aadd! (g w rw/W-CALLBACKS) [(fn [_ _] (h pub)) [nil false]])
            nil))))
    (unwind! ek)))

(defn savepoint [_ _] (throw (ex-info "savepoint outside a body" {})))

(defn- pub-act [w pub]
  (let [a (get (g w rw/W-FWD) (:act pub))]
    (rv w (or a (some #(when (== (id-of %) (long (:act pub))) %) (some-> (g w rw/W-SAVEPOINTS) hs/oset-vals))))))

(defn resume!
  "S2: continues the publication's own world with `v`, at most once."
  [pub v]
  (let [w (:world pub)]
    (when (compare-and-set! (:state pub) :pending :resumed)
      (gated w
        (let [a (pub-act w pub)]
          (if (and a (sp-deliver! w a [v false]))
            (commit! w [:resume-savepoint (:act pub) [:opaque v]])
            (refuse! w [:resume-savepoint (:act pub) [:opaque v]])))))
    nil))

(defn abandon!
  "S7: cancels the run suspended at the publication with err ::abandoned."
  [pub]
  (let [w (:world pub)]
    (when (compare-and-set! (:state pub) :pending :abandoned)
      (gated w
        (when-let [a (pub-act w pub)]
          (let [r (rv w (g a rw/A-RUN))]
            (when-let [sps (g w rw/W-SAVEPOINTS)] (hs/oset-del! sps (:act pub)))
            (cancel! w r ::abandoned)
            (commit! w [:abandon-savepoint (:act pub)])))))
    nil))

(defn instantiate
  "S3: a frozen fork of the publication's basis, not yet activated: the
   run's copy is parked on its savepoint, which is the fork's pending
   activation. Any number of instances are independent."
  [pub]
  (let [b (:basis pub)
        c (fork-world* b)]
    (s! c rw/W-PENDING-ACT (:act pub))
    c))

(defn activate!
  "S4: resumes an instantiated fork's pending activation with `v`."
  [w v]
  (gated w
    (let [aid (g w rw/W-PENDING-ACT)]
      (when aid
        (s! w rw/W-PENDING-ACT nil)
        (let [a (rv w (get (g w rw/W-FWD) aid
                           (some #(when (== (id-of %) (long aid)) %)
                                 (concat (g w rw/W-SP-DORMANT)
                                         (some-> (g w rw/W-SAVEPOINTS) hs/oset-vals)))))]
          (if (and a (sp-deliver! w a [v false]))
            (commit! w [:activate aid [:opaque v]])
            (refuse! w [:activate aid [:opaque v]]))))))
  w)

(defn offload [_] (throw (ex-info "offload outside a body" {})))

(defn sleep [_] (throw (ex-info "sleep outside a body" {})))

(defn track [_] (throw (ex-info "track outside a body" {})))
(defn await [_] (throw (ex-info "await outside a body" {})))
(defn await-all [_] (throw (ex-info "await-all outside a body" {})))
(defn take! [_] (throw (ex-info "take! outside a body" {})))
(defn acquire! [_] (throw (ex-info "acquire! outside a body" {})))
(defn await-any [_] (throw (ex-info "await-any outside a body" {})))

;; ---------------------------------------------------------------------------
;; Body macros (partial-cps)

#?(:clj
   (do
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-track [_ctx r e]
       (fn [[x]] `(track-effect! (row-of ~x) ~r ~e)))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-await [_ctx r e]
       (fn [[x]] `(await-effect! (row-of ~x) ~r ~e)))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-await-all [_ctx r e]
       (fn [[xs]] `(await-all-effect! ~xs ~r ~e)))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-await-any [_ctx r e]
       (fn [[xs]] `(await-any-effect! ~xs ~r ~e)))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-savepoint [_ctx r e]
       (fn [[site payload]] `(savepoint-effect! ~site ~payload ~r ~e)))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-fork [_ctx r e]
       (fn [_] `(fork-effect! ~r ~e)))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-offload [_ctx r e]
       (fn [[f]] `(offload-effect! ~f ~r ~e)))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-sleep [_ctx r e]
       (fn [[ms]] `(sleep-effect! ~ms ~r ~e)))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-consume [_ctx r e]
       (fn [[x]] `(consume-effect! (row-of ~x) ~r ~e)))
     (def ^:private breakpoints
       {'org.replikativ.spindel.v2.core/track `bp-track
        'org.replikativ.spindel.v2.core/await `bp-await
        'org.replikativ.spindel.v2.core/await-all `bp-await-all
        'org.replikativ.spindel.v2.core/await-any `bp-await-any
        'org.replikativ.spindel.v2.core/take! `bp-consume
        'org.replikativ.spindel.v2.core/offload `bp-offload
        'org.replikativ.spindel.v2.core/fork `bp-fork
        'org.replikativ.spindel.v2.core/savepoint `bp-savepoint
        'org.replikativ.spindel.v2.core/sleep `bp-sleep
        'org.replikativ.spindel.v2.core/acquire! `bp-consume})
     (declare register-finally)
     (defn- catch-or-finally? [x] (and (seq? x) (#{'catch 'finally} (first x))))
     (defn- opaque-head? [h]
       (or (#{'quote 'fn 'fn* 'reify 'deftype 'proxy 'letfn 'letfn*} h)
           (and (symbol? h)
                (let [v (resolve h)]
                  (and (var? v)
                       (#{'org.replikativ.spindel.v2.core/spin 'org.replikativ.spindel.v2.core/task}
                        (symbol (str (.-ns ^clojure.lang.Var v)) (str (.-sym ^clojure.lang.Var v)))))))))
     (defn- has-finally?
       "Whether a form contains a `try` with a `finally` outside closures."
       [form]
       (and (seq? form)
            (or (and (= 'try (first form)) (some #(and (seq? %) (= 'finally (first %))) form))
                (and (not (opaque-head? (first form))) (some has-finally? form)))))
     (def ^:private ^:dynamic *env* nil)
     (defn- user-macro
       "The macro var a form calls, unless it is a local, a special form, our
        own body macro, or the target is ClojureScript."
       [h]
       (when (and (symbol? h) (not (contains? *env* h)) (not (special-symbol? h))
                  (not (:ns *env*)))
         (let [v (resolve h)]
           (when (and (var? v) (:macro (meta v)) (not (opaque-head? h))
                      (not (#{'org.replikativ.spindel.v2.core/with-scope}
                            (symbol (str (.-ns ^clojure.lang.Var v)) (str (.-sym ^clojure.lang.Var v))))))
             v))))
     (defn- register-finally
       "Body contract (§7): each `try` with a `finally` registers its region
        with the run, so cancellation can unwind through it (T14). A user
        macro whose expansion has one (`with-open`, `binding`, ...) is
        expanded so its region registers too (JVM). Nested bodies and
        closures are left alone (they register their own)."
       [form]
       (cond
         (seq? form)
         (let [h (first form)
               mv (user-macro h)
               expanded (when mv (apply @mv form *env* (rest form)))]
           (cond
             (opaque-head? h) form
             (and expanded (has-finally? expanded)) (register-finally expanded)
             (= 'try h)
             (let [clauses (map register-finally (rest form))
                   [body cfs] (split-with (complement catch-or-finally?) clauses)]
               (if (some #(= 'finally (first %)) cfs)
                 (with-meta
                   `(~'try (do (enter-finally!) ~@body)
                     ~@(map (fn [c] (if (= 'finally (first c))
                                      (list* 'finally `(exit-finally!) (rest c))
                                      c))
                            cfs))
                   (meta form))
                 (with-meta (cons 'try clauses) (meta form))))
             :else (with-meta (apply list (map register-finally form)) (meta form))))
         (vector? form) (with-meta (mapv register-finally form) (meta form))
         (map? form) (with-meta (into {} (map (fn [[k v]] [(register-finally k) (register-finally v)])) form) (meta form))
         (set? form) (with-meta (into #{} (map register-finally) form) (meta form))
         :else form))
     (defn- body-fn [env body]
       (let [r (gensym "r") e (gensym "e")
             params {:r r :e e :env env :breakpoints breakpoints
                     :opaque-scopes #{`spin `task}}]
         `(fn [~r ~e] ~(ioc/invert params (binding [*env* env] (register-finally (cons 'do body)))))))
     (def empty-inputs (object-array 0))
     (defn- inputs-form
       "The captured values as an array, built without an intermediate vector."
       [frees]
       (if (empty? frees)
         `empty-inputs
         (let [a (with-meta (gensym "in") {:tag 'objects})]
           `(let [~a (object-array ~(count frees))]
              ~@(map-indexed (fn [i x] `(aset ~a ~i ~x)) frees)
              ~a))))
     (defn- site-of [form]
       (bit-and 0x3fffffff (hash [(str *ns*) (:line (meta form)) (:column (meta form))])))
     (defmacro spin
       "A cached reactive computation (T3). Inside a body it is created in the
        running computation's basis and adopted by later runs."
       [& body]
       (let [frees (vec (sort-by str (filter symbol? (free-vars/free-variables-or-all &env (cons 'do body)))))]
         `(create-comp! ~(site-of &form) ~(inputs-form frees) ~(body-fn &env body))))
     (defmacro with-scope
       "An explicit scope (T16): tasks spawned inside are owned by it and are
        cancelled when it closes, at normal exit, on error or on cancel."
       [& body]
       (let [s (gensym "scope")]
         `(let [~s (open-scope!)]
            (~'try (do (enter-finally!) ~@body)
              (~'finally (exit-finally!) (close-scope-fx! ~s))))))
     (defmacro task
       "A task (T4): started at once; structured child of the creating run."
       [& body]
       (let [frees (vec (sort-by str (filter symbol? (free-vars/free-variables-or-all &env (cons 'do body)))))]
         `(spawn! ~(site-of &form) ~(inputs-form frees) ~(body-fn &env body))))))
