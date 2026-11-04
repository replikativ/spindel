(ns org.replikativ.spindel.v2fwd
  "THROWAWAY hot-path prototype for engine v2 (docs/engine-v2-spec.md §10).
   Measures the cost of the v2 hot path against missionary; it is not an
   engine. No forks, savepoints, cancellation trees or weak handles.

   Kept from the spec:
   - mutable rows (object arrays), edges with in-place reuse across runs;
   - dirty-count scheduling (§4.5): a computation runs only when every dirty
     debtor has settled; no event queue for local completions;
   - lazy invalidation of unobserved computations (Q2) via hot counts;
   - lexical activation: effects receive their computation from the body
     closure, so no ThreadLocal or binding per slice;
   - one gate per world (a lock on JVM);
   - children created in a run are owned by it and retired, with their
     edges, when the parent re-runs (Rule R);
   - tasks: one-shot waits, no edges, nothing retained after completion."
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.runtime :as pr]
            [org.replikativ.spindel.incremental.interval :as iv]
            #?(:clj [is.simm.partial-cps.ioc :as ioc]))
  #?(:cljs (:require-macros [org.replikativ.spindel.v2fwd :refer [g s! gated cmp task alist acount anth aadd! apop! aput!]])))

;; ---------------------------------------------------------------------------
;; Row access

#?(:clj
   (do
     (defmacro g [row i]
       ;; read through the world's view: one epoch compare; the forward-map
       ;; lookup is never taken in an unforked world
       (let [s (with-meta (gensym "row") {:tag 'objects})]
         `(let [~s (resolve-row ~row)] (aget ~s ~i))))
     (defmacro s! [row i v]
       (let [s (with-meta (gensym "row") {:tag 'objects})]
         (if (some? (:ns &env))
           `(let [~s ~row] (aset ~s ~i ~v))
           `(let [~s (own-row ~row)] (clojure.lang.RT/aset ~s (int ~i) (clojure.lang.RT/box ~v))))))
     (defn- cljs? [env] (some? (:ns env)))
     (defn- al [] (with-meta (gensym "l") {:tag 'java.util.ArrayList}))
     (defmacro alist [] (if (cljs? &env) `(cljs.core/array) `(java.util.ArrayList.)))
     (defmacro acount [l] (if (cljs? &env) `(.-length ~l) (let [x (al)] `(let [~x ~l] (.size ~x)))))
     (defmacro anth [l i] (if (cljs? &env) `(aget ~l ~i) (let [x (al)] `(let [~x ~l] (.get ~x (int ~i))))))
     (defmacro aadd! [l v] (if (cljs? &env) `(.push ~l ~v) (let [x (al)] `(let [~x ~l] (.add ~x (clojure.lang.RT/box ~v))))))
     (defmacro apop! [l] (if (cljs? &env) `(.pop ~l)
                             (let [x (al)] `(let [~x ~l] (.remove ~x (int (dec (.size ~x))))))))
     (defmacro aput! [l i v] (if (cljs? &env) `(aset ~l ~i ~v) (let [x (al)] `(let [~x ~l] (.set ~x (int ~i) (clojure.lang.RT/box ~v))))))))

;; Owner epochs (forward-map variant): every row's slot 0 of an extra
;; header array is not available, so the epoch is kept in the row's last slot.
(def ^{:tag 'longs} world-epoch (long-array 1))
(def ^{:tag 'objects} forward (object-array 1))   ; persistent map old-row -> copy (unused unforked)

(defn resolve-row ^objects [^objects r]
  (if (or (nil? r) (== (aget world-epoch 0) (long (aget r (dec (alength r))))))
    r
    (let [m (aget forward 0)] (or (get m r) r))))

(defn own-row ^objects [^objects r]
  (if (== (aget world-epoch 0) (long (aget r (dec (alength r)))))
    r
    (throw (ex-info "fork writes not implemented in the tax probe" {}))))

;; Kinds
(def ^:const K-SOURCE 0)
(def ^:const K-COMP 1)
(def ^:const K-TASK 2)
(def ^:const K-DEFERRED 3)

;; States of a computation
(def ^:const ST-COLD 0)     ; never run
(def ^:const ST-CLEAN 1)
(def ^:const ST-DIRTY 2)    ; marked; waits for PENDING debtors
(def ^:const ST-RUNNING 3)
(def ^:const ST-PARKED 4)
(def ^:const ST-RETIRED 5)

;; Row fields (shared layout; each kind uses a subset)
(def ^:const KIND 0)
(def ^:const BODY 1)
(def ^:const STATE 2)
(def ^:const RESULT 3)      ; result / source value / deferred value
(def ^:const ERROR 4)       ; result is an error
(def ^:const INS 5)         ; edges this computation reads
(def ^:const OUTS 6)        ; edges reading this row
(def ^:const CURSOR 7)      ; next INS position in the current run
(def ^:const PENDING 8)     ; dirty debtors not yet settled
(def ^:const MUST 9)        ; some settled debtor changed
(def ^:const OBSERVERS 10)
(def ^:const HOT 11)        ; observers + hot creditors
(def ^:const WAITERS 12)    ; parked [row resolve reject]
(def ^:const RESOLVE 13)
(def ^:const REJECT 14)
(def ^:const WORLD 15)
(def ^:const CHILDREN 16)
(def ^:const RERUN 17)      ; changed while running or parked
(def ^:const ROW-SIZE 18)

;; Edge fields
(def ^:const E-DEBTOR 0)
(def ^:const E-CRED 1)
(def ^:const E-IDX 2)       ; position in debtor OUTS
(def ^:const E-MARK 3)      ; contributed to creditor PENDING
(def ^:const E-BASE 4)      ; last value read (track baseline)

;; World fields
(def ^:const W-LOCK 0)
(def ^:const W-READY 1)
(def ^:const W-DRAINING 2)
(def ^:const W-WRITES 3)

(defn world []
  (doto (object-array 5)
    (aset 4 (Long/valueOf 0))
    (aset W-LOCK #?(:clj (java.util.concurrent.locks.ReentrantLock.) :cljs nil))
    (aset W-READY (alist))
    (aset W-DRAINING false)
    (aset W-WRITES (alist))))

(def ^:dynamic *world* nil)

#?(:clj
   (defmacro gated [w & body]
     (if (cljs? &env)
       `(do ~@body)
       `(let [~(with-meta 'gw {:tag 'objects}) ~w
              ~(with-meta 'gl {:tag 'java.util.concurrent.locks.ReentrantLock}) (aget ~'gw W-LOCK)]
          (.lock ~'gl)
          (try ~@body (finally (.unlock ~'gl)))))))

(defn- force! [x]
  (loop [x x]
    (if (pr/thunk? x) (recur (pr/force-thunk x)) x)))

;; ---------------------------------------------------------------------------
;; Edges and hot counts

(declare inc-hot! dec-hot! dec-pending! complete!)

(defn- hot? [row] (pos? (long (g row HOT))))

(defn- link! [debtor cred]
  (let [outs (g debtor OUTS)
        e (doto (object-array 6) (aset 5 (Long/valueOf 0)))]
    (s! e E-DEBTOR debtor) (s! e E-CRED cred) (s! e E-IDX (acount outs)) (s! e E-MARK false)
    (aadd! outs e)
    (when (hot? cred) (inc-hot! debtor))
    e))

(defn- unlink! [e]
  (let [debtor (g e E-DEBTOR)
        cred (g e E-CRED)
        outs (g debtor OUTS)
        i (long (g e E-IDX))
        last-e (apop! outs)]
    (when-not (identical? last-e e)
      (aput! outs i last-e) (s! last-e E-IDX i))
    (when (hot? cred) (dec-hot! debtor))
    (when (g e E-MARK)
      (s! e E-MARK false)
      (dec-pending! cred))))

(defn- schedule! [row]
  (aadd! (g (g row WORLD) W-READY) row))

(defn- inc-hot! [row]
  (let [h (inc (long (g row HOT)))]
    (s! row HOT h)
    (when (and (== h 1) (== K-COMP (long (g row KIND))))
      (let [ins (g row INS)]
        (dotimes [i (acount ins)] (inc-hot! (g (anth ins i) E-DEBTOR))))
      (when (and (== ST-DIRTY (long (g row STATE))) (zero? (long (g row PENDING))) (g row MUST))
        (schedule! row)))))

(defn- dec-hot! [row]
  (let [h (dec (long (g row HOT)))]
    (s! row HOT h)
    (when (and (zero? h) (== K-COMP (long (g row KIND))))
      (let [ins (g row INS)]
        (dotimes [i (acount ins)] (dec-hot! (g (anth ins i) E-DEBTOR)))))))

;; ---------------------------------------------------------------------------
;; Invalidation (§4.5): mark the dirty region first, then settle

(defn- mark! [e]
  (s! e E-MARK true)
  (let [cred (g e E-CRED)
        st (long (g cred STATE))]
    (s! cred PENDING (inc (long (g cred PENDING))))
    (cond
      (== st ST-CLEAN)
      (do (s! cred STATE ST-DIRTY) (s! cred MUST false)
          (let [outs (g cred OUTS)]
            (dotimes [i (acount outs)] (mark! (anth outs i)))))
      (or (== st ST-RUNNING) (== st ST-PARKED))
      (s! cred RERUN true))))

(defn- resume-waiters! [row]
  (when-let [ws (g row WAITERS)]
    (s! row WAITERS nil)
    (let [v (g row RESULT) err? (g row ERROR)]
      (dotimes [i (acount ws)]
        (let [^objects w (anth ws i)
              waiter (aget w 0)]
          (when-not (== ST-RETIRED (long (g waiter STATE)))
            (when (== K-COMP (long (g waiter KIND))) (s! waiter STATE ST-RUNNING))
            (force! (try ((aget w (if err? 2 1)) v)
                         (catch #?(:clj Throwable :cljs :default) t ((g waiter REJECT) t))))))))))

(defn- settle! [row changed?]
  (let [outs (g row OUTS)]
    (dotimes [i (acount outs)]
      (let [e (anth outs i)]
        (when (g e E-MARK)
          (s! e E-MARK false)
          (let [cred (g e E-CRED)]
            (when changed? (s! cred MUST true))
            (dec-pending! cred)))))))

(defn- dec-pending! [row]
  (let [p (dec (long (g row PENDING)))]
    (s! row PENDING p)
    (when (and (zero? p) (== ST-DIRTY (long (g row STATE))))
      (if (g row MUST)
        (if (hot? row)
          (schedule! row)
          (settle! row true))           ; lazy (Q2): stays dirty until demanded
        (do (s! row STATE ST-CLEAN)
            (resume-waiters! row)
            (settle! row false))))))

;; ---------------------------------------------------------------------------
;; Runs

(defn- retire! [row]
  (s! row STATE ST-RETIRED)
  (let [ins (g row INS)]
    (dotimes [i (acount ins)] (unlink! (anth ins i)))
    (s! row INS (alist)))
  (s! row WAITERS nil)
  (when-let [cs (g row CHILDREN)]
    (s! row CHILDREN nil)
    (dotimes [i (acount cs)] (retire! (anth cs i)))))

(defn- run-row! [row]
  (when-let [cs (g row CHILDREN)]
    (s! row CHILDREN nil)
    (dotimes [i (acount cs)] (retire! (anth cs i))))
  (s! row STATE ST-RUNNING) (s! row CURSOR 0) (s! row MUST false) (s! row RERUN false)
  (force! (try ((g row BODY) row (g row RESOLVE) (g row REJECT))
               (catch #?(:clj Throwable :cljs :default) t ((g row REJECT) t)))))

(defn- drain! [w]
  (when-not (g w W-DRAINING)
    (s! w W-DRAINING true)
    (try
      (let [ready (g w W-READY)]
        (loop [i 0]
          (when (< i (acount ready))
            (let [row (anth ready i)]
              (when (and (== ST-DIRTY (long (g row STATE))) (zero? (long (g row PENDING))) (g row MUST))
                (run-row! row)))
            (recur (inc i))))
        #?(:clj (.clear ^java.util.ArrayList ready) :cljs (set! (.-length ready) 0)))
      (finally (s! w W-DRAINING false)))))

(defn- complete! [row v err?]
  (let [ins (g row INS)
        k (long (g row CURSOR))]
    (loop [] (when (> (acount ins) k) (unlink! (apop! ins)) (recur))))
  (let [changed? (or err? (not (== ST-RUNNING (long (g row STATE)))) ; parked runs resumed set RUNNING
                     (not= v (g row RESULT)))
        first? (identical? ::none (g row RESULT))]
    (s! row RESULT v) (s! row ERROR err?) (s! row STATE ST-CLEAN)
    (when (or changed? first?)
      (when-let [obs (g row OBSERVERS)]
        (dotimes [i (acount obs)]
          (let [^objects o (anth obs i)] ((aget o (if err? 1 0)) v)))))
    (resume-waiters! row)
    (settle! row (or changed? first?))
    (when (g row RERUN)
      (s! row RERUN false)
      (s! row STATE ST-DIRTY) (s! row MUST true)
      (when (hot? row) (schedule! row)))
    nil))

(defn make-comp [w parent body]
  (let [row (doto (object-array (inc ROW-SIZE)) (aset ROW-SIZE (Long/valueOf 0)))]
    (s! row KIND K-COMP) (s! row BODY body) (s! row STATE ST-COLD) (s! row RESULT ::none)
    (s! row ERROR false) (s! row INS (alist)) (s! row OUTS (alist)) (s! row CURSOR 0)
    (s! row PENDING 0) (s! row MUST false) (s! row HOT 0) (s! row WORLD w) (s! row RERUN false)
    (s! row RESOLVE (fn [v] (complete! row v false)))
    (s! row REJECT (fn [e] (complete! row e true)))
    (when parent
      (when-not (g parent CHILDREN) (s! parent CHILDREN (alist)))
      (aadd! (g parent CHILDREN) row))
    row))

(defn- finish-task! [row v err?]
  (s! row STATE ST-CLEAN) (s! row RESULT v) (s! row ERROR err?) (s! row BODY nil)
  (resume-waiters! row)
  (when-let [cb (g row OBSERVERS)]
    (s! row OBSERVERS nil)
    ((aget ^objects cb (if err? 1 0)) v))
  nil)

(defn make-task [w body]
  (let [row (doto (object-array (inc ROW-SIZE)) (aset ROW-SIZE (Long/valueOf 0)))]
    (s! row KIND K-TASK) (s! row BODY body) (s! row STATE ST-COLD) (s! row WORLD w)
    (s! row RESOLVE (fn [v] (finish-task! row v false)))
    (s! row REJECT (fn [e] (finish-task! row e true)))
    row))

(defn source [w v]
  (let [row (doto (object-array (inc ROW-SIZE)) (aset ROW-SIZE (Long/valueOf 0)))]
    (s! row KIND K-SOURCE) (s! row RESULT v) (s! row OUTS (alist)) (s! row HOT 0) (s! row WORLD w)
    (s! row STATE ST-CLEAN)
    row))

(defn deferred [w]
  (let [row (doto (object-array (inc ROW-SIZE)) (aset ROW-SIZE (Long/valueOf 0)))]
    (s! row KIND K-DEFERRED) (s! row STATE ST-COLD) (s! row WORLD w)
    row))

;; ---------------------------------------------------------------------------
;; Effects

(defn- record-dep! [self x]
  (let [ins (g self INS)
        k (long (g self CURSOR))
        n (acount ins)]
    (s! self CURSOR (inc k))
    (if (and (< k n) (identical? x (g (anth ins k) E-DEBTOR)))
      (anth ins k)
      (do (loop [] (when (> (acount ins) k) (unlink! (apop! ins)) (recur)))
          (let [e (link! x self)] (aadd! ins e) e)))))

(defn- park! [self x r e]
  (when-not (g x WAITERS) (s! x WAITERS (alist)))
  (aadd! (g x WAITERS) (doto (object-array 3) (aset 0 self) (aset 1 r) (aset 2 e)))
  (when (== K-COMP (long (g self KIND))) (s! self STATE ST-PARKED))
  nil)

(defn track-effect! [self src r e]
  (let [v (g src RESULT)]
    (if (== K-COMP (long (g self KIND)))
      (let [edge (record-dep! self src)
            old (g edge E-BASE)]
        (s! edge E-BASE v)
        (r (iv/->Interval old v nil)))
      (r (iv/->Interval nil v nil)))))      ; Q1: a task's track is a snapshot read

(defn await-effect! [self x r e]
  (let [xk (long (g x KIND))]
    (when (and (== K-COMP xk) (== K-COMP (long (g self KIND))))
      (record-dep! self x))
    (let [st (long (g x STATE))]
      (cond
        (== st ST-CLEAN) (if (g x ERROR) (e (g x RESULT)) (r (g x RESULT)))
        (== xk K-DEFERRED) (park! self x r e)
        :else
        (do (when (or (== st ST-COLD)
                      (and (== st ST-DIRTY) (zero? (long (g x PENDING))) (g x MUST)))
              (run-row! x))
            (if (== ST-CLEAN (long (g x STATE)))
              (if (g x ERROR) (e (g x RESULT)) (r (g x RESULT)))
              (park! self x r e)))))))

#?(:clj
   (do
     (def ^:private self-sym (symbol "__v2self"))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-track [_ctx r e]
       (fn [[x]] `(track-effect! ~self-sym ~x ~r ~e)))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-await [_ctx r e]
       (fn [[x]] `(await-effect! ~self-sym ~x ~r ~e)))
     (def ^:private breakpoints
       {'org.replikativ.spindel.v2fwd/track `bp-track
        'org.replikativ.spindel.v2fwd/await `bp-await})
     (defn- cps-fn [body env]
       (let [r (gensym "r") e (gensym "e")
             params {:r r :e e :env env :breakpoints breakpoints
                     :opaque-scopes #{`cmp `task}}]
         `(fn [~self-sym ~r ~e] ~(ioc/invert params (cons 'do body)))))
     (defmacro cmp
       "A cached reactive computation. Inside another body it is owned by the
        enclosing run."
       [& body]
       (let [nested? (contains? (or (:locals &env) &env) self-sym)]
         `(make-comp ~(if nested? `(g ~self-sym WORLD) `*world*)
                     ~(when nested? self-sym)
                     ~(cps-fn body &env))))
     (defmacro task
       "A one-shot task, started when awaited or `run-task!`."
       [& body]
       (let [nested? (contains? (or (:locals &env) &env) self-sym)]
         `(make-task ~(if nested? `(g ~self-sym WORLD) `*world*) ~(cps-fn body &env))))))

(defn track [_] (throw (ex-info "track outside a body" {})))
(defn await [_] (throw (ex-info "await outside a body" {})))

;; ---------------------------------------------------------------------------
;; Host API

(defn- process-writes! [w]
  (let [ws (g w W-WRITES)]
    (loop []
      (when (pos? (acount ws))
        (let [batch #?(:clj (.remove ^java.util.ArrayList ws (int 0)) :cljs (.shift ws))]
          (let [[src v] batch]
            (s! src RESULT v)
            (let [outs (g src OUTS)]
              (dotimes [i (acount outs)] (mark! (anth outs i))))
            (settle! src true)
            (drain! w)))
        (recur)))))

(defn set-source! [src v]
  (let [w (g src WORLD)]
    (gated w
      (if (g w W-DRAINING)
        (aadd! (g w W-WRITES) [src v])
        (do (s! src RESULT v)
            (let [outs (g src OUTS)]
              (dotimes [i (acount outs)] (mark! (anth outs i))))
            (settle! src true)
            (drain! w)
            (when (pos? (acount (g w W-WRITES))) (process-writes! w)))))
    nil))

(defn observe!
  "Attach a host observer; returns a cancel fn."
  [row on-value on-error]
  (let [w (g row WORLD)
        o (doto (object-array 2) (aset 0 on-value) (aset 1 on-error))]
    (gated w
      (when-not (g row OBSERVERS) (s! row OBSERVERS (alist)))
      (aadd! (g row OBSERVERS) o)
      (inc-hot! row)
      (let [st (long (g row STATE))]
        (cond
          (== st ST-COLD) (run-row! row)
          (== st ST-CLEAN) ((aget o (if (g row ERROR) 1 0)) (g row RESULT))))
      (drain! w))
    (fn []
      (gated w
        (let [obs (g row OBSERVERS)
              i #?(:clj (.indexOf ^java.util.ArrayList obs o) :cljs (.indexOf obs o))]
          (when-not (neg? i)
            #?(:clj (.remove ^java.util.ArrayList obs (int i)) :cljs (.splice obs i 1))
            (dec-hot! row)))))))

(defn run-task!
  "Start a task; `on-value`/`on-error` receive its outcome once."
  [row on-value on-error]
  (gated (g row WORLD)
    (s! row OBSERVERS (doto (object-array 2) (aset 0 on-value) (aset 1 on-error)))
    (run-row! row))
  nil)

(defn deliver! [d v]
  (gated (g d WORLD)
    (when (== ST-COLD (long (g d STATE)))
      (s! d RESULT v) (s! d ERROR false) (s! d STATE ST-CLEAN)
      (resume-waiters! d)
      (drain! (g d WORLD))))
  nil)

(defn value
  "Host read of a computation that completes synchronously."
  [row]
  (gated (g row WORLD)
    (let [st (long (g row STATE))]
      (when (or (== st ST-COLD) (and (== st ST-DIRTY) (g row MUST)))
        (run-row! row)))
    (if (== ST-CLEAN (long (g row STATE)))
      (g row RESULT)
      (throw (ex-info "computation did not complete synchronously" {})))))

(defn row-state [row] (g row STATE))
(defn out-count [row] (acount (g row OUTS)))
