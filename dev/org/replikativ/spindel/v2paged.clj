(ns org.replikativ.spindel.v2paged
  "THROWAWAY representation spike for M5 (.internal/m5-forks-design.md and the
   sol review): the v2spike hot path with rows referenced by integer id through
   a per-world page directory, intrusive id-linked edge lists, and per-row
   owner epochs for copy-on-write forks.

   Same algorithm as v2spike (dirty counts, lazy hot counts, edge reuse by
   cursor, children retired on re-run), so the paired difference measures the
   representation. JVM only.

   Copy-on-write:
   - reads go through the directory and never copy;
   - a write first `own!`s the row: a row whose epoch is not the world's is
     copied, its page copied if the page is shared, the directory copied if
     shared;
   - `fork` is O(directory length): both worlds get fresh epochs, so every
     existing row, page and the directory become a frozen shared basis."
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.runtime :as pr]
            [is.simm.partial-cps.ioc :as ioc]
            [org.replikativ.spindel.incremental.interval :as iv]))

(set! *warn-on-reflection* true)

;; ---------------------------------------------------------------------------
;; Directory, pages, ownership

(def ^:const PAGE-BITS 8)
(def ^:const PAGE 256)
(def ^:const PAGE-MASK 255)

;; World
(def ^:const W-EPOCH 0)      ; long
(def ^:const W-DIR 1)        ; Object[]: pages; slot (alength-1) holds the dir epoch
(def ^:const W-NEXT 2)       ; java.util.concurrent.atomic.AtomicLong (family counter)
(def ^:const W-READY 3)      ; ArrayList of ids (world-local, never shared)
(def ^:const W-DRAINING 4)
(def ^:const W-EPOCHS 5)     ; AtomicLong: family epoch source
(def ^:const W-SIZE 6)

;; Rows: slot 0 = owner epoch, then fields; references are Long ids, 0 = none
(def ^:const EPOCH 0)
(def ^:const KIND 1)
;; computation / source
(def ^:const BODY 2)
(def ^:const STATE 3)
(def ^:const RESULT 4)
(def ^:const ERROR 5)
(def ^:const INS-HEAD 6)     ; first dep edge of this computation (its reads)
(def ^:const INS-TAIL 7)
(def ^:const OUTS-HEAD 8)    ; first edge reading this row
(def ^:const CURSOR 9)       ; next edge id to reuse in the current run (0 = append)
(def ^:const PENDING 10)
(def ^:const MUST 11)
(def ^:const HOT 12)
(def ^:const OBS 13)         ; persistent vector of [on-value on-error]
(def ^:const WAITERS 14)     ; persistent vector of [id resolve reject]
(def ^:const CHILDREN 15)    ; persistent vector of ids
(def ^:const RERUN 16)
(def ^:const ROW-SIZE 17)
;; edge
(def ^:const E-DEBTOR 2)
(def ^:const E-CRED 3)
(def ^:const E-OUT-NEXT 4)   ; next edge in the debtor's OUTS
(def ^:const E-OUT-PREV 5)
(def ^:const E-IN-NEXT 6)    ; next edge in the creditor's INS
(def ^:const E-IN-PREV 7)
(def ^:const E-MARK 8)
(def ^:const E-BASE 9)
(def ^:const EDGE-SIZE 10)

(def ^:const K-SOURCE 0)
(def ^:const K-COMP 1)
(def ^:const K-EDGE 2)

(def ^:const ST-COLD 0)
(def ^:const ST-CLEAN 1)
(def ^:const ST-DIRTY 2)
(def ^:const ST-RUNNING 3)
(def ^:const ST-PARKED 4)
(def ^:const ST-RETIRED 5)

(defn- hinted [prefix] (with-meta (gensym prefix) {:tag 'objects}))

(defn- dir-epoch ^long [^objects dir] (long (aget dir (dec (alength dir)))))
(defn- page-epoch ^long [^objects page] (long (aget page PAGE)))

(defmacro row
  "The world's view of row `id` (read-only unless owned)."
  [w id]
  (let [ws (hinted "w") d (hinted "d") pg (hinted "p") i (gensym "i")]
    `(let [~ws ~w
           ~d (aget ~ws W-DIR)
           ~i (long ~id)
           ~pg (aget ~d (unchecked-int (bit-shift-right ~i PAGE-BITS)))]
       (aget ~pg (unchecked-int (bit-and ~i PAGE-MASK))))))

(defmacro gf [r i] (let [x (hinted "r")] `(let [~x ~r] (aget ~x ~i))))
(defmacro gl [r i] (let [x (hinted "r")] `(let [~x ~r] (long (aget ~x ~i)))))
(defmacro sf! [r i v] (let [x (hinted "r")] `(let [~x ~r] (clojure.lang.RT/aset ~x (int ~i) (clojure.lang.RT/box ~v)))))

;; Boxed ids are interned once per id, so writing a reference allocates nothing.
(def ^objects boxes (object-array (bit-shift-left 1 22)))
(defn box-id ^Object [^long id]
  (let [b (aget boxes (unchecked-int id))]
    (if (nil? b) (let [l (Long. id)] (aset boxes (unchecked-int id) l) l) b)))
(defmacro sfid! [r i id] (let [x (hinted "r")] `(let [~x ~r] (aset ~x (int ~i) (box-id ~id)))))

(defn- own-dir! ^objects [^objects w]
  (let [^objects dir (aget w W-DIR)
        ep (long (aget w W-EPOCH))]
    (if (== ep (dir-epoch dir))
      dir
      (let [d (aclone dir)]
        (aset d (dec (alength d)) (Long/valueOf ep))
        (aset w W-DIR d)
        d))))

(defn- own-page! ^objects [^objects w ^long pi]
  (let [^objects dir (own-dir! w)
        ^objects page (aget dir (unchecked-int pi))
        ep (long (aget w W-EPOCH))]
    (if (== ep (page-epoch page))
      page
      (let [p (aclone page)]
        (aset p PAGE (Long/valueOf ep))
        (aset dir (unchecked-int pi) p)
        p))))

(defn own!
  "The world's own copy of row `id`, copying it (and its page and the
   directory) on first write after a fork."
  ^objects [^objects w ^long id]
  (let [^objects r (row w id)
        ep (long (aget w W-EPOCH))]
    (if (== ep (long (aget r EPOCH)))
      r
      (let [^objects page (own-page! w (bit-shift-right id PAGE-BITS))
            c (aclone r)]
        (aset c EPOCH (Long/valueOf ep))
        (aset page (unchecked-int (bit-and id PAGE-MASK)) c)
        c))))

(defn- grow-dir! [^objects w ^long pi]
  (let [^objects dir (own-dir! w)
        n (dec (alength dir))]
    (when (>= pi n)
      (let [d (object-array (inc (* 2 (max 1 (inc pi)))))]
        (System/arraycopy dir 0 d 0 n)
        (aset d (dec (alength d)) (aget dir n))
        (aset w W-DIR d)))))

(defn- alloc!
  "A new row with a fresh family id, owned by this world."
  ^long [^objects w ^objects r]
  (let [id (.incrementAndGet ^java.util.concurrent.atomic.AtomicLong (aget w W-NEXT))
        pi (bit-shift-right id PAGE-BITS)
        ep (long (aget w W-EPOCH))]
    (grow-dir! w pi)
    (let [^objects dir (own-dir! w)]
      (when (nil? (aget dir (unchecked-int pi)))
        (let [p (object-array (inc PAGE))]
          (aset p PAGE (Long/valueOf ep))
          (aset dir (unchecked-int pi) p))))
    (aset r EPOCH (Long/valueOf ep))
    (let [^objects page (own-page! w pi)]
      (aset page (unchecked-int (bit-and id PAGE-MASK)) r))
    id))

(defn world []
  (let [w (object-array W-SIZE)
        epochs (java.util.concurrent.atomic.AtomicLong. 0)
        ep (.incrementAndGet epochs)
        dir (object-array 9)]
    (aset dir 8 (Long/valueOf ep))
    (doto w
      (aset W-EPOCH (Long/valueOf ep))
      (aset W-DIR dir)
      (aset W-NEXT (java.util.concurrent.atomic.AtomicLong. 0))
      (aset W-READY (java.util.ArrayList.))
      (aset W-DRAINING false)
      (aset W-EPOCHS epochs))))

(defn fork
  "A frozen fork: both worlds get fresh epochs, so all current storage becomes
   a shared basis. O(1) here (no copy at all); the directory is copied on the
   first write of each world."
  [^objects w]
  (let [^java.util.concurrent.atomic.AtomicLong epochs (aget w W-EPOCHS)
        child (aclone w)]
    (aset w W-EPOCH (Long/valueOf (.incrementAndGet epochs)))
    (aset child W-EPOCH (Long/valueOf (.incrementAndGet epochs)))
    (aset child W-READY (java.util.ArrayList.))
    (aset child W-DRAINING false)
    child))

(def ^:dynamic *world* nil)
(def active (object-array 1))   ; the world executing (single-threaded spike)
(defn active-world [] (aget ^objects active 0))

(defn- force! [x] (loop [x x] (if (pr/thunk? x) (recur (pr/force-thunk x)) x)))

;; ---------------------------------------------------------------------------
;; Edges (intrusive lists by id)

(declare inc-hot! dec-hot! dec-pending! complete!)

(defn- hot? [^objects w ^long id] (pos? (gl (row w id) HOT)))

(defn- link!
  "A new edge debtor -> cred, appended to cred's INS and pushed on debtor's OUTS."
  ^long [^objects w ^long debtor ^long cred]
  (let [e (object-array EDGE-SIZE)]
    (sf! e KIND K-EDGE)
    (sfid! e E-DEBTOR debtor) (sfid! e E-CRED cred) (sf! e E-MARK false)
    (sfid! e E-OUT-PREV 0) (sfid! e E-IN-NEXT 0)
    (let [eid (alloc! w e)
          ^objects d (own! w debtor)
          head (gl d OUTS-HEAD)]
      (sfid! e E-OUT-NEXT head)
      (when-not (zero? head) (sfid! (own! w head) E-OUT-PREV eid))
      (sfid! d OUTS-HEAD eid)
      (let [^objects c (own! w cred)
            tail (gl c INS-TAIL)
            e (own! w eid)]
        (sfid! e E-IN-PREV tail)
        (if (zero? tail) (sfid! c INS-HEAD eid) (sf! (own! w tail) E-IN-NEXT eid))
        (sfid! c INS-TAIL eid))
      (when (hot? w cred) (inc-hot! w debtor))
      eid)))

(defn- unlink!
  "Removes edge `eid` from both lists."
  [^objects w ^long eid]
  (let [^objects e (row w eid)
        debtor (gl e E-DEBTOR) cred (gl e E-CRED)
        on (gl e E-OUT-NEXT) op (gl e E-OUT-PREV)
        in (gl e E-IN-NEXT) ip (gl e E-IN-PREV)]
    (if (zero? op) (sfid! (own! w debtor) OUTS-HEAD on) (sf! (own! w op) E-OUT-NEXT on))
    (when-not (zero? on) (sfid! (own! w on) E-OUT-PREV op))
    (if (zero? ip) (sfid! (own! w cred) INS-HEAD in) (sf! (own! w ip) E-IN-NEXT in))
    (if (zero? in) (sfid! (own! w cred) INS-TAIL ip) (sf! (own! w in) E-IN-PREV ip))
    (when (hot? w cred) (dec-hot! w debtor))
    (when (gf e E-MARK)
      (sf! (own! w eid) E-MARK false)
      (dec-pending! w cred))))

(defn- truncate-ins!
  "Removes cred's INS edges from `from` (an edge id) to the tail."
  [^objects w ^long cred ^long from]
  (loop [eid from]
    (when-not (zero? eid)
      (let [nxt (gl (row w eid) E-IN-NEXT)]
        (unlink! w eid)
        (recur nxt)))))

(defn- schedule! [^objects w ^long id]
  (.add ^java.util.ArrayList (aget w W-READY) (Long/valueOf id)))

(defn- inc-hot! [^objects w ^long id]
  (let [^objects r (own! w id)
        h (inc (gl r HOT))]
    (sf! r HOT h)
    (when (and (== h 1) (== K-COMP (gl r KIND)))
      (loop [eid (gl r INS-HEAD)]
        (when-not (zero? eid)
          (let [^objects e (row w eid)]
            (inc-hot! w (gl e E-DEBTOR))
            (recur (gl e E-IN-NEXT)))))
      (let [^objects r (row w id)]
        (when (and (== ST-DIRTY (gl r STATE)) (zero? (gl r PENDING)) (gf r MUST))
          (schedule! w id))))))

(defn- dec-hot! [^objects w ^long id]
  (let [^objects r (own! w id)
        h (dec (gl r HOT))]
    (sf! r HOT h)
    (when (and (zero? h) (== K-COMP (gl r KIND)))
      (loop [eid (gl r INS-HEAD)]
        (when-not (zero? eid)
          (let [^objects e (row w eid)]
            (dec-hot! w (gl e E-DEBTOR))
            (recur (gl e E-IN-NEXT))))))))

;; ---------------------------------------------------------------------------
;; Mark and settle

(defn- mark! [^objects w ^long eid]
  (sf! (own! w eid) E-MARK true)
  (let [cred (gl (row w eid) E-CRED)
        ^objects c (own! w cred)
        st (gl c STATE)]
    (sf! c PENDING (inc (gl c PENDING)))
    (cond
      (== st ST-CLEAN)
      (do (sf! c STATE ST-DIRTY) (sf! c MUST false)
          (loop [o (gl c OUTS-HEAD)]
            (when-not (zero? o)
              (let [nxt (gl (row w o) E-OUT-NEXT)]
                (mark! w o)
                (recur nxt)))))
      (or (== st ST-RUNNING) (== st ST-PARKED))
      (sf! c RERUN true))))

(defn- resume-waiters! [^objects w ^long id]
  (let [^objects r (row w id)
        ws (gf r WAITERS)]
    (when (seq ws)
      (sf! (own! w id) WAITERS [])
      (let [^objects r (row w id)
            v (gf r RESULT) err? (gf r ERROR)]
        (doseq [[waiter ok ko] ws]
          (let [^objects wr (row w waiter)]
            (when-not (== ST-RETIRED (gl wr STATE))
              (sf! (own! w waiter) STATE ST-RUNNING)
              (aset ^objects active 0 w)
              (force! (try ((if err? ko ok) v)
                           (catch Throwable t (complete! w waiter t true)))))))))))

(defn- settle! [^objects w ^long id changed?]
  (loop [o (gl (row w id) OUTS-HEAD)]
    (when-not (zero? o)
      (let [^objects e (row w o)
            nxt (gl e E-OUT-NEXT)]
        (when (gf e E-MARK)
          (sf! (own! w o) E-MARK false)
          (let [cred (gl e E-CRED)]
            (when changed? (sf! (own! w cred) MUST true))
            (dec-pending! w cred)))
        (recur nxt)))))

(defn- dec-pending! [^objects w ^long id]
  (let [^objects r (own! w id)
        p (dec (gl r PENDING))]
    (sf! r PENDING p)
    (when (and (zero? p) (== ST-DIRTY (gl r STATE)))
      (if (gf r MUST)
        (if (hot? w id)
          (schedule! w id)
          (settle! w id true))
        (do (sf! r STATE ST-CLEAN)
            (resume-waiters! w id)
            (settle! w id false))))))

;; ---------------------------------------------------------------------------
;; Runs

(defn- retire! [^objects w ^long id]
  (let [^objects r (own! w id)]
    (sf! r STATE ST-RETIRED)
    (truncate-ins! w id (gl r INS-HEAD))
    (sf! (own! w id) WAITERS [])
    (let [cs (gf (row w id) CHILDREN)]
      (sf! (own! w id) CHILDREN [])
      (doseq [c cs] (retire! w c)))))

(defn- run-row! [^objects w ^long id]
  (let [cs (gf (row w id) CHILDREN)]
    (when (seq cs)
      (sf! (own! w id) CHILDREN [])
      (doseq [c cs] (retire! w c))))
  (let [^objects r (own! w id)]
    (sfid! r STATE ST-RUNNING) (sf! r CURSOR (gl r INS-HEAD)) (sf! r MUST false) (sf! r RERUN false)
    (aset ^objects active 0 w)
    (force! (try ((gf r BODY) id (fn [v] (complete! (aget ^objects active 0) id v false))
                  (fn [e] (complete! (aget ^objects active 0) id e true)))
                 (catch Throwable t (complete! w id t true))))))

(defn- drain! [^objects w]
  (when-not (aget w W-DRAINING)
    (aset w W-DRAINING true)
    (try
      (let [^java.util.ArrayList ready (aget w W-READY)]
        (loop [i 0]
          (when (< i (.size ready))
            (let [id (long (.get ready i))
                  ^objects r (row w id)]
              (when (and (== ST-DIRTY (gl r STATE)) (zero? (gl r PENDING)) (gf r MUST))
                (run-row! w id)))
            (recur (inc i))))
        (.clear ready))
      (finally (aset w W-DRAINING false)))))

(defn- complete! [^objects w ^long id v err?]
  (let [cur (gl (row w id) CURSOR)]
    (when-not (zero? cur) (truncate-ins! w id cur)))
  (let [^objects r (row w id)
        changed? (or err? (not (== ST-RUNNING (gl r STATE))) (not= v (gf r RESULT)))
        first? (identical? ::none (gf r RESULT))
        ^objects r (own! w id)]
    (sf! r RESULT v) (sf! r ERROR err?) (sf! r STATE ST-CLEAN)
    (when (or changed? first?)
      (doseq [[ok ko] (gf r OBS)] ((if err? ko ok) v)))
    (resume-waiters! w id)
    (settle! w id (or changed? first?))
    (when (gf (row w id) RERUN)
      (let [^objects r (own! w id)]
        (sf! r RERUN false) (sf! r STATE ST-DIRTY) (sf! r MUST true))
      (when (hot? w id) (schedule! w id)))
    nil))

(defn- new-row [kind]
  (let [r (object-array ROW-SIZE)]
    (sf! r KIND kind) (sf! r STATE ST-COLD) (sf! r RESULT ::none) (sf! r ERROR false)
    (sfid! r INS-HEAD 0) (sfid! r INS-TAIL 0) (sfid! r OUTS-HEAD 0) (sf! r CURSOR 0)
    (sf! r PENDING 0) (sf! r MUST false) (sf! r HOT 0) (sf! r OBS []) (sf! r WAITERS [])
    (sf! r CHILDREN []) (sf! r RERUN false)
    r))

(defn make-comp [^objects w parent body]
  (let [r (new-row K-COMP)]
    (sf! r BODY body)
    (let [id (alloc! w r)]
      (when parent
        (let [^objects p (own! w parent)] (sf! p CHILDREN (conj (gf p CHILDREN) id))))
      id)))

(defn source [^objects w v]
  (let [r (new-row K-SOURCE)]
    (sf! r RESULT v) (sf! r STATE ST-CLEAN)
    (alloc! w r)))

;; ---------------------------------------------------------------------------
;; Effects

(defn- record-dep! [^objects w ^long self ^long x]
  (let [cur (gl (row w self) CURSOR)]
    (if (and (not (zero? cur)) (== x (gl (row w cur) E-DEBTOR)))
      (do (sfid! (own! w self) CURSOR (gl (row w cur) E-IN-NEXT)) cur)
      (do (when-not (zero? cur) (truncate-ins! w self cur))
          (sfid! (own! w self) CURSOR 0)
          (link! w x self)))))

(defn- park! [^objects w self x r e]
  (let [self (long self) x (long x) ^objects xr (own! w x)]
    (sf! xr WAITERS (conj (gf xr WAITERS) [self r e])))
  (sf! (own! w self) STATE ST-PARKED)
  nil)

(defn track-effect! [self src r e]
  (let [^objects w (aget ^objects active 0)
        self (long self) src (long src)
        eid (record-dep! w self src)
        v (gf (row w src) RESULT)
        old (gf (row w eid) E-BASE)]
    (sf! (own! w eid) E-BASE v)
    (r (iv/->Interval old v nil))))

(defn await-effect! [self x r e]
  (let [^objects w (aget ^objects active 0)
        self (long self) x (long x)]
    (record-dep! w self x)
    (let [st (gl (row w x) STATE)]
      (cond
        (== st ST-CLEAN) (let [^objects xr (row w x)] (if (gf xr ERROR) (e (gf xr RESULT)) (r (gf xr RESULT))))
        :else
        (do (when (or (== st ST-COLD)
                      (let [^objects xr (row w x)]
                        (and (== st ST-DIRTY) (zero? (gl xr PENDING)) (gf xr MUST))))
              (run-row! w x)
              (aset ^objects active 0 w))
            (let [^objects xr (row w x)]
              (if (== ST-CLEAN (gl xr STATE))
                (if (gf xr ERROR) (e (gf xr RESULT)) (r (gf xr RESULT)))
                (park! w self x r e))))))))

(def ^:private self-sym (symbol "__v2pself"))
(defn ^:is.simm.partial-cps.ioc/eager-arguments bp-track [_ctx r e]
  (fn [[x]] `(track-effect! ~self-sym ~x ~r ~e)))
(defn ^:is.simm.partial-cps.ioc/eager-arguments bp-await [_ctx r e]
  (fn [[x]] `(await-effect! ~self-sym ~x ~r ~e)))
(def ^:private breakpoints
  {'org.replikativ.spindel.v2paged/track `bp-track
   'org.replikativ.spindel.v2paged/await `bp-await})

(defmacro cmp [& body]
  (let [r (gensym "r") e (gensym "e")
        nested? (contains? (or (:locals &env) &env) self-sym)
        params {:r r :e e :env &env :breakpoints breakpoints :opaque-scopes #{`cmp}}]
    `(make-comp ~(if nested? `(active-world) `*world*)
                ~(when nested? self-sym)
                (fn [~self-sym ~r ~e] ~(ioc/invert params (cons 'do body))))))

(defn track [_] (throw (ex-info "track outside a body" {})))
(defn await [_] (throw (ex-info "await outside a body" {})))

;; ---------------------------------------------------------------------------
;; Host API

(defn set-source! [^objects w id v]
  (let [id (long id)]
    (sf! (own! w id) RESULT v)
    (loop [o (gl (row w id) OUTS-HEAD)]
      (when-not (zero? o)
        (let [nxt (gl (row w o) E-OUT-NEXT)]
          (mark! w o)
          (recur nxt))))
    (settle! w id true)
    (drain! w)
    nil))

(defn observe! [^objects w id on-value on-error]
  (let [id (long id)
        ^objects r (own! w id)]
    (sf! r OBS (conj (gf r OBS) [on-value on-error]))
    (inc-hot! w id)
    (let [st (gl (row w id) STATE)]
      (cond (== st ST-COLD) (run-row! w id)
            (== st ST-CLEAN) (let [^objects r (row w id)] ((if (gf r ERROR) on-error on-value) (gf r RESULT)))))
    (drain! w)
    (fn [] (let [^objects r (own! w id)]
             (sf! r OBS (vec (remove #(identical? on-value (first %)) (gf r OBS))))
             (dec-hot! w id)))))

(defn value [^objects w id] (gf (row w (long id)) RESULT))
(defn out-count [^objects w id]
  (loop [o (gl (row w (long id)) OUTS-HEAD) n 0]
    (if (zero? o) n (recur (gl (row w o) E-OUT-NEXT) (inc n)))))
