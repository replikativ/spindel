(ns org.replikativ.spindel.v2.core
  "Engine v2, layer 1 core (docs/engine-v2-spec.md). M1 scope: sources
   (signal, cell), computations, observe, pins, Rule R by retention counts.

   One world executes one slice at a time (D0). Every host entry takes the
   world gate, performs its transition, then drains: resumptions, eligible
   dispatches and Rule R, until nothing is left. Host callbacks run after
   the drain."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.rows :as rw
             #?@(:clj [:refer [g s! gl alist acount anth aadd! apop! aput! aclear! acopy]])]
            [org.replikativ.spindel.incremental.interval :as iv]
            [is.simm.partial-cps.runtime :as pr]
            #?(:clj [is.simm.partial-cps.ioc :as ioc])
            #?(:clj [org.replikativ.spindel.engine.free-vars :as free-vars]))
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.rows :refer [g s! gl alist acount anth aadd! apop! aput! aclear! acopy]]
                            [org.replikativ.spindel.v2.core :refer [gated commit!]])))

#?(:clj (set! *warn-on-reflection* true))

(declare drain! demand! settle! pending-zero! rule-r! complete! fail! validate!
         deliver-observe! value)

;; ---------------------------------------------------------------------------
;; Active run (B6: continuations close over no engine object)

#?(:clj (def ^ThreadLocal active-tl (ThreadLocal.))
   :cljs (def active-cell #js {:run nil}))

(defn active-run []
  #?(:clj (.get active-tl) :cljs (.-run active-cell)))

(defn- set-active! [r]
  #?(:clj (.set active-tl r) :cljs (set! (.-run active-cell) r)))

;; ---------------------------------------------------------------------------
;; World, ids, gate

(def ^:dynamic *world* nil)

(defn- alloc-id! ^long [w]
  (let [^longs n (g w rw/W-NEXT)
        id (aget n 0)]
    (aset n 0 (inc id))
    id))

(defn- register! [w row]
  (when-let [reg (g w rw/W-REG)]
    (.put ^java.util.Map reg (g row rw/ID) row))
  row)

(defn- unregister! [w row]
  (when-let [reg (g w rw/W-REG)]
    (.remove ^java.util.Map reg (g row rw/ID)))
  nil)

(defn world
  "A new world. `:verify? true` keeps an id->row registry and a commit log
   (test only)."
  ([] (world {}))
  ([{:keys [verify? hook]}]
   (let [w (object-array rw/W-SIZE)
         next (long-array 1)]
     (aset next 0 1)
     (s! w rw/TYPE rw/T-WORLD)
     (s! w rw/W-LOCK #?(:clj (java.util.concurrent.locks.ReentrantLock.) :cljs nil))
     (s! w rw/W-NEXT next)
     (s! w rw/W-READY (alist))
     (s! w rw/W-RESUME (alist))
     (s! w rw/W-DRAINING false)
     (s! w rw/W-RQ (alist))
     (s! w rw/W-PINS #?(:clj (java.util.IdentityHashMap.) :cljs (js/Map.)))
     (s! w rw/W-CALLBACKS (alist))
     (when verify?
       (s! w rw/W-REG #?(:clj (java.util.LinkedHashMap.) :cljs (js/Map.)))
       (s! w rw/W-LOG (alist))
       (s! w rw/W-INTERN #?(:clj (java.util.IdentityHashMap.) :cljs (js/Map.)))
       (s! w rw/W-HOOK hook))
     (s! w rw/ID (alloc-id! w))
     (let [root (object-array rw/S-SIZE)]
       (s! root rw/TYPE rw/T-SCOPE)
       (s! root rw/ID (alloc-id! w))
       (s! root rw/S-PARENT nil)
       (s! root rw/S-KIND :root)
       (s! root rw/S-OPEN true)
       (s! w rw/W-ROOT root)
       (register! w root))
     w)))

#?(:clj
   (defmacro gated [w & body]
     (if (rw/cljs? &env)
       `(do ~@body)
       (let [gw (with-meta (gensym "gw") {:tag 'objects})
             lk (with-meta (gensym "lock") {:tag 'java.util.concurrent.locks.ReentrantLock})]
         `(let [~gw ~w
                ~lk (aget ~gw rw/W-LOCK)]
            (.lock ~lk)
            (try ~@body (finally (.unlock ~lk))))))))

(defn- force! [x]
  (loop [x x]
    (if (pr/thunk? x) (recur (pr/force-thunk x)) x)))

;; ---------------------------------------------------------------------------
;; Commit log (verify mode only, §11.4)

(defn logging? [w] (some? (g w rw/W-LOG)))

(defn log-commit! [w item]
  (let [log (g w rw/W-LOG)]
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
(defn- source? [row] (== rw/T-SOURCE (gl row rw/TYPE)))

(defn- live? [c]
  (and (not (g c rw/C-IDLE))
       (some? (g c rw/C-DONE-EPOCH))
       (== (gl c rw/C-DONE-EPOCH) (gl c rw/C-EPOCH))
       (zero? (gl c rw/C-PENDING))))

(defn- current? [c r]
  (and (some? r) (== (gl r rw/R-EPOCH) (gl c rw/C-EPOCH))))

(defn- needs-run? [c]
  (and (not (g c rw/C-IDLE))
       (not (and (some? (g c rw/C-DONE-EPOCH))
                 (== (gl c rw/C-DONE-EPOCH) (gl c rw/C-EPOCH))))
       (not (current? c (g c rw/C-RUN)))))

(defn- hot? [row] (pos? (gl row rw/HOT)))

(defn- maybe-schedule!
  "§4.5.7: a hot needs-run computation whose dirty debtors have settled is
   queued for dispatch. (Blocked debtors arrive with M2.)"
  [c]
  (when (and (needs-run? c) (zero? (gl c rw/C-PENDING)) (hot? c) (not (g c rw/C-QUEUED)))
    (s! c rw/C-QUEUED true)
    (aadd! (g (g c rw/WORLD) rw/W-READY) c)))

;; ---------------------------------------------------------------------------
;; Retention counts and demand (§3, §10.8, §10.10)

(defn- ref-inc! [row] (s! row rw/REFS (inc (gl row rw/REFS))))

(defn- ref-dec! [row]
  (let [n (dec (gl row rw/REFS))]
    (s! row rw/REFS n)
    (when (zero? n) (aadd! (g (g row rw/WORLD) rw/W-RQ) row))))

(declare hot-inc! hot-dec!)

(defn- hot-inc! [row]
  (let [h (inc (gl row rw/HOT))]
    (s! row rw/HOT h)
    (when (and (== h 1) (comp? row))
      (let [ins (g row rw/C-INS)]
        (dotimes [i (acount ins)] (hot-inc! (g (anth ins i) rw/E-DEBTOR))))
      (maybe-schedule! row))))

(defn- hot-dec! [row]
  (let [h (dec (gl row rw/HOT))]
    (s! row rw/HOT h)
    (when (and (zero? h) (comp? row))
      (let [ins (g row rw/C-INS)]
        (dotimes [i (acount ins)] (hot-dec! (g (anth ins i) rw/E-DEBTOR)))))))

(defn- demands? [e]
  (let [k (gl e rw/E-KIND)]
    (or (== k rw/EK-OBSERVE) (== k rw/EK-WAIT)
        (and (== k rw/EK-DEP) (hot? (g e rw/E-CRED))))))

;; ---------------------------------------------------------------------------
;; Edges

(defn- link!
  "A new edge on `debtor`. It retains the debtor (§3.2) and demands it when
   its creditor is demanded."
  [w kind cred debtor at]
  (let [e (object-array rw/E-SIZE)
        outs (g debtor rw/OUTS)]
    (s! e rw/TYPE rw/T-EDGE)
    (s! e rw/ID (alloc-id! w))
    (s! e rw/E-KIND kind)
    (s! e rw/E-CRED cred)
    (s! e rw/E-DEBTOR debtor)
    (s! e rw/E-AT at)
    (s! e rw/E-ARMED true)
    (s! e rw/E-MARKED false)
    (s! e rw/E-IDX (acount outs))
    (aadd! outs e)
    (ref-inc! debtor)
    (when (demands? e) (hot-inc! debtor))
    (register! w e)))

(defn- unmark! [e]
  (when (g e rw/E-MARKED)
    (s! e rw/E-MARKED false)
    (let [c (g e rw/E-CRED)
          p (dec (gl c rw/C-PENDING))]
      (s! c rw/C-PENDING p)
      (when (zero? p) (pending-zero! c)))))

(defn- unlink!
  "Removes an edge. A marked edge discharges its mark (X#1)."
  [w e]
  (let [debtor (g e rw/E-DEBTOR)
        outs (g debtor rw/OUTS)
        i (gl e rw/E-IDX)
        last-e (apop! outs)]
    (when-not (identical? last-e e)
      (aput! outs i last-e)
      (s! last-e rw/E-IDX i))
    (when (demands? e) (hot-dec! debtor))
    (s! e rw/E-ACT nil)
    (unregister! w e)
    (unmark! e)
    (ref-dec! debtor)))

;; ---------------------------------------------------------------------------
;; Mark and settle (§4.5)

(defn- mark-from!
  "§4.5.1: marks every dep out-edge of the computations reachable from `d`."
  [d]
  (let [outs (g d rw/OUTS)]
    (dotimes [i (acount outs)]
      (let [e (anth outs i)]
        (when (and (== rw/EK-DEP (gl e rw/E-KIND)) (not (g e rw/E-MARKED)))
          (s! e rw/E-MARKED true)
          (let [c (g e rw/E-CRED)]
            (s! c rw/C-PENDING (inc (gl c rw/C-PENDING)))
            (mark-from! c)))))))

(defn- invalidate!
  "A dep fire that is not a delivery (§4.5.3): an epoch step."
  [e]
  (s! e rw/E-ARMED false)
  (let [c (g e rw/E-CRED)]
    (s! c rw/C-EPOCH (inc (gl c rw/C-EPOCH)))
    (mark-from! c)
    (maybe-schedule! c)))

(defn- debtor-result
  "[value err?] of a settled debtor."
  [d]
  (if (comp? d)
    [(g d rw/C-RESULT) (boolean (g d rw/C-ERR))]
    [(g d rw/X-VALUE) false]))

(defn- fill!
  "T9 delivery into the activation `a` that `e` is an unfilled member of."
  [w e a]
  (let [r (g a rw/A-RUN)
        c (g e rw/E-CRED)
        d (g e rw/E-DEBTOR)]
    (when (and (current? c r) (== rw/ACT-PARKED (gl r rw/R-ACT)))   ; §4.5.4
      (s! e rw/E-ACT nil)
      (s! e rw/E-ARMED true)
      (s! e rw/E-SEEN (g d rw/VERSION))
      (let [^objects sl (g a rw/A-SLOTS)] (aset sl (int (g e rw/E-SLOT)) (debtor-result d)))
      (let [n (dec (gl a rw/A-REMAINING))]
        (s! a rw/A-REMAINING n)
        (when (and (zero? n) (not (g a rw/A-INLINE)))
          (aadd! (g w rw/W-RESUME) a))))))

(defn- fire-dep!
  "T9 on a dep edge whose debtor changed."
  [w e]
  (when (g e rw/E-ARMED)
    (let [a (g e rw/E-ACT)]
      (if (and a (current? (g e rw/E-CRED) (g a rw/A-RUN)))
        (fill! w e a)
        (invalidate! e)))))

(defn- settle!
  "§4.5.2: `d` became live. Changed out-edges fire before they are unmarked;
   unfilled members of a current activation are delivered either way (Z#20)."
  [w d]
  (let [outs (acopy (g d rw/OUTS))
        ver (g d rw/VERSION)]
    (dotimes [i (acount outs)]
      (let [e (anth outs i)
            k (gl e rw/E-KIND)]
        (cond
          (== k rw/EK-DEP)
          (do (if-let [a (g e rw/E-ACT)]
                (fill! w e a)
                (when (not= ver (g e rw/E-SEEN)) (fire-dep! w e)))
              (unmark! e))
          (== k rw/EK-OBSERVE) (deliver-observe! w e)
          (== k rw/EK-WAIT)
          (let [cb (g e rw/E-CRED)]
            (unlink! w e)
            (aadd! (g w rw/W-CALLBACKS) [cb (debtor-result d)])))))))

(defn- pending-zero! [c]
  (cond
    (live? c) (settle! (g c rw/WORLD) c)
    :else (maybe-schedule! c)))

;; ---------------------------------------------------------------------------
;; Observe delivery (§4.2)

(defn- deliver-observe! [w e]
  (let [d (g e rw/E-DEBTOR)
        ver (g d rw/VERSION)
        seen (g e rw/E-SEEN)]
    (when (or (nil? seen) (> (long ver) (long seen)))
      (s! e rw/E-SEEN ver)
      (aadd! (g w rw/W-CALLBACKS) [(g e rw/E-CRED) (debtor-result d)]))))

;; ---------------------------------------------------------------------------
;; Runs

(defn- new-run! [w c epoch]
  (let [r (object-array rw/R-SIZE)]
    (s! r rw/TYPE rw/T-RUN)
    (s! r rw/ID (alloc-id! w))
    (s! r rw/R-SCOPE (alloc-id! w))          ; run scope id (Z: T5/T11 order run, scope)
    (s! r rw/R-WORLD w)
    (s! r rw/R-OF c)
    (s! r rw/R-EPOCH epoch)
    (s! r rw/R-ACT rw/ACT-ACTIVE)
    (s! r rw/R-MODE 0)
    (s! r rw/R-SLICE false)
    (s! r rw/R-EIDX 0)
    (s! r rw/R-CURSOR 0)
    (s! c rw/C-RUN r)
    (register! w r)))

(defn- retire! [w r]
  (let [c (g r rw/R-OF)]
    (when (identical? r (g c rw/C-RUN)) (s! c rw/C-RUN nil))
    (unregister! w r)))

(defn- cancel-replace!
  "T14 `cancel(R, replace)`: affects only the run (Y#2). M1 runs hold no
   finalizers or resources, so the run retires at once."
  [w r]
  (when-not (== rw/ACT-DONE (gl r rw/R-ACT))
    (s! r rw/R-ACT rw/ACT-DONE)
    (s! r rw/R-MODE 1)
    (when-let [a (g r rw/R-ACTV)]
      (s! r rw/R-ACTV nil)
      ;; dep members stay with the computation (W#2)
      (let [ins (g (g r rw/R-OF) rw/C-INS)]
        (dotimes [i (acount ins)]
          (let [e (anth ins i)] (when (identical? a (g e rw/E-ACT)) (s! e rw/E-ACT nil)))))
      (unregister! w a))
    (when-not (g r rw/R-SLICE) (retire! w r))))

(defn- slice!
  "Runs `f` as a slice of `r` on the host stack, restoring the caller's
   active run afterwards (I10)."
  [r f]
  (let [prev (active-run)]
    (s! r rw/R-SLICE true)
    (set-active! r)
    (try
      (try (force! (f)) (catch #?(:clj Throwable :cljs :default) t (fail! (or (active-run) r) t)))
      (finally
        (s! r rw/R-SLICE false)
        (set-active! prev)
        (when (== rw/ACT-DONE (gl r rw/R-ACT)) (retire! (g r rw/R-WORLD) r))))))

(defn- ok-k [v] (complete! (active-run) v false))
(defn- err-k [t] (complete! (active-run) t true))
(defn- fail! [r t] (complete! r t true))

(defn- release-adoption! [w c]
  (when-let [ab (g c rw/C-ADOPT)]
    (s! c rw/C-ADOPT nil)
    (dotimes [i (acount ab)] (ref-dec! (anth ab i))))
  (when-let [bs (g c rw/C-ADOPT-BASE)]
    (s! c rw/C-ADOPT-BASE nil)
    (dotimes [i (acount bs)] (ref-dec! (g (anth bs i) rw/E-DEBTOR)))))

(defn- complete!
  "T12."
  [r v err?]
  (when (and r (== rw/ACT-ACTIVE (gl r rw/R-ACT)))
    (let [w (g r rw/R-WORLD)
          c (g r rw/R-OF)]
      (s! r rw/R-ACT rw/ACT-DONE)
      (when (current? c r)
        (let [changed? (or (nil? (g c rw/C-DONE-EPOCH))
                           (not= (boolean err?) (boolean (g c rw/C-ERR)))
                           (not= v (g c rw/C-RESULT)))]
          (when changed?
            (s! c rw/VERSION (inc (gl c rw/VERSION)))
            (s! c rw/C-RESULT v)
            (s! c rw/C-ERR (boolean err?)))
          (s! c rw/C-DONE-EPOCH (g r rw/R-EPOCH))
          (release-adoption! w c)))
      (commit! w [:complete (g r rw/ID) (if err? :err :ok)])
      (when (live? c) (settle! w c))))
  nil)

;; ---------------------------------------------------------------------------
;; Dispatch (T5, T11)

(defn- earliest-fired [c]
  (let [ins (g c rw/C-INS)]
    (loop [i 0]
      (when (< i (acount ins))
        (let [e (anth ins i)]
          (if (g e rw/E-ARMED) (recur (inc i)) i))))))

(defn- dispatch!
  "T11 (and T5 for a computation without a fired edge): starts the
   computation's next run, re-entering at its earliest fired dep edge when
   that site is re-entrant (X#2)."
  [w c]
  (s! c rw/C-QUEUED false)
  (when (needs-run? c)
    (when-let [old (g c rw/C-RUN)] (cancel-replace! w old))
    (let [ins (g c rw/C-INS)
          restart? (g c rw/C-RESTART)
          ei (when-not restart? (earliest-fired c))
          e (when ei (anth ins ei))
          at (if e (gl e rw/E-AT) -1)]
      (s! c rw/C-RESTART false)
      ;; Suffix: dep edges after E move their baselines to adoption (§4.4) and
      ;; keep retaining their debtors there (Z#21).
      (let [keep (if ei (inc (long ei)) (if restart? 0 (acount ins)))]
        (when (> (acount ins) keep)
          (let [bs (or (g c rw/C-ADOPT-BASE) (alist))]
            (loop []
              (when (> (acount ins) keep)
                (let [x (apop! ins)]
                  (ref-inc! (g x rw/E-DEBTOR))
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
              (let [x (anth basis i)]
                (if (or restart? (> (gl x rw/AT) at)) (aadd! ab x) (aadd! kept x))))
            (s! c rw/C-BASIS kept)
            (s! c rw/C-ADOPT ab))))
      (let [r (new-run! w c (g c rw/C-EPOCH))
            k (when e (g e rw/E-CONT))]
        (commit! w [:dispatch (g c rw/ID) (g r rw/ID)])
        (if (and e k)
          ;; Resume E's continuation with E's delivery; E is consumed (re-armed).
          (let [d (g e rw/E-DEBTOR)]
            ;; Creation ordinals continue after the prefix creations.
            (when-let [basis (g c rw/C-BASIS)]
              (when (pos? (acount basis))
                (let [ords #?(:clj (java.util.HashMap.) :cljs (js/Map.))]
                  (dotimes [i (acount basis)]
                    (let [key (gl (anth basis i) rw/KEY)
                          site (bit-shift-right key 32)
                          nxt (inc (bit-and key 0xffffffff))
                          cur (long (or (.get ords site) 0))]
                      (when (> nxt cur) #?(:clj (.put ords site nxt) :cljs (.set ords site nxt)))))
                  (s! r rw/R-ORD ords))))
            (s! r rw/R-CURSOR (inc (long ei)))
            (s! r rw/R-EIDX (inc at))
            (s! e rw/E-ARMED true)
            (s! e rw/E-SEEN (g d rw/VERSION))
            (if (source? d)
              (let [old (g e rw/E-BASE) v (g d rw/X-VALUE)]
                (s! e rw/E-BASE v)
                (slice! r #(k (iv/->Interval old v nil))))
              (let [[v err?] (debtor-result d)]
                (slice! r (if err? #((g e rw/E-ERRK) v) #(k v))))))
          ;; Restart from the body. E (if any) is re-armed; its baseline advances
          ;; when the new run reads it (Z#22).
          (do (when e (s! e rw/E-ARMED true))
              (slice! r #((g c rw/C-BODY) ok-k err-k))))))))

;; ---------------------------------------------------------------------------
;; Body effects

(defn- current-comp-run []
  (let [r (active-run)]
    (when-not r (throw (ex-info "effect outside a body" {})))
    r))

(defn- next-at! ^long [r]
  (let [at (gl r rw/R-EIDX)]
    (s! r rw/R-EIDX (inc at))
    at))

(defn- adoption-baseline!
  "Consumes a suffix baseline for (at, d) (§4.4)."
  [c at d]
  (when-let [bs (g c rw/C-ADOPT-BASE)]
    (loop [i 0]
      (when (< i (acount bs))
        (let [x (anth bs i)]
          (if (and (== at (gl x rw/E-AT)) (identical? d (g x rw/E-DEBTOR)))
            (do (aput! bs i (anth bs (dec (acount bs))))
                (apop! bs)
                (ref-dec! d)
                x)
            (recur (inc i))))))))

(defn- site-edge!
  "The dep edge of `c` at site `at` on `d`: reused when the prefix already
   has it, otherwise created. Returns [edge reused?]."
  [w r c d at k ek]
  (let [ins (g c rw/C-INS)
        cur (gl r rw/R-CURSOR)]
    (s! r rw/R-CURSOR (inc cur))
    (if (and (< cur (acount ins))
             (== at (gl (anth ins cur) rw/E-AT))
             (identical? d (g (anth ins cur) rw/E-DEBTOR)))
      (let [e (anth ins cur)]
        (s! e rw/E-CONT k) (s! e rw/E-ERRK ek)
        [e true])
      (let [_ (loop []                          ; a diverged prefix: drop the rest
                (when (> (acount ins) cur) (unlink! w (apop! ins)) (recur)))
            e (link! w rw/EK-DEP c d at)]
        (s! e rw/E-CONT k) (s! e rw/E-ERRK ek)
        (aadd! ins e)
        [e false]))))

(defn- reentrant-k
  "§2: `cont` is the continuation only for `one` awaits in a run without
   finalizers or resources."
  [r k]
  (when (and (nil? (g r rw/R-FINS)) (nil? (g r rw/R-RES))) k))

(defn track-effect!
  "T7."
  [x k ek]
  (let [r (current-comp-run)
        w (g r rw/R-WORLD)
        c (g r rw/R-OF)
        at (next-at! r)
        [e reused?] (site-edge! w r c x at (reentrant-k r k) ek)
        v (g x rw/X-VALUE)
        old (if reused?
              (g e rw/E-BASE)
              (when-let [b (adoption-baseline! c at x)] (g b rw/E-BASE)))
        iv (if (or reused? (some? old) (some? (g e rw/E-SEEN)))
             (iv/->Interval old v nil)
             (iv/->Interval nil v nil))]
    (s! e rw/E-BASE v)
    (s! e rw/E-SEEN (g x rw/VERSION))
    (s! e rw/E-ARMED true)
    (commit! w [:track (g r rw/ID) (g x rw/ID) (g e rw/ID)])
    (k iv)))

(defn- resume-inline! [w r a k ek]
  (s! r rw/R-ACTV nil)
  (s! r rw/R-ACT rw/ACT-ACTIVE)
  (s! r rw/R-SLICE true)
  (set-active! r)
  (unregister! w a)
  (commit! w [:resume (g a rw/ID)])
  (let [[v err?] (let [^objects sl (g a rw/A-SLOTS)] (aget sl 0))]
    (if err? (ek v) (k v))))

(defn await-effect!
  "T6 with mode `one` on a computation or a source."
  [d k ek]
  (let [r (current-comp-run)
        w (g r rw/R-WORLD)
        c (g r rw/R-OF)
        at (next-at! r)
        aid (alloc-id! w)
        [e _] (site-edge! w r c d at (reentrant-k r k) ek)]
    (when (source? d) (s! e rw/E-BASE (g d rw/X-VALUE)))
    (when (and (comp? d) (g d rw/C-IDLE)) (validate! w d))
    (if (or (source? d) (live? d))
      (do (s! e rw/E-SEEN (g d rw/VERSION))
          (commit! w [:await (g r rw/ID) [(g d rw/ID)] :one aid])
          (let [[v err?] (debtor-result d)]
            (if err? (ek v) (k v))))
      (let [a (object-array rw/A-SIZE)]
        (s! a rw/TYPE rw/T-ACT)
        (s! a rw/ID aid)
        (s! a rw/A-RUN r)
        (s! a rw/A-MODE :one)
        (s! a rw/A-SLOTS (object-array 1))
        (s! a rw/A-REMAINING 1)
        (s! a rw/A-R k)
        (s! a rw/A-E ek)
        (s! a rw/A-INLINE true)
        (register! w a)
        (s! e rw/E-ACT a)
        (s! e rw/E-SLOT 0)
        (s! r rw/R-ACTV a)
        (s! r rw/R-ACT rw/ACT-PARKED)
        (s! r rw/R-SLICE false)
        (commit! w [:await (g r rw/ID) [(g d rw/ID)] :one aid])
        ;; The demanded debtor's first slice runs on the host stack (I10).
        (demand! w d)
        (if (and (zero? (gl a rw/A-REMAINING)) (current? c r))
          (resume-inline! w r a k ek)
          (do (s! a rw/A-INLINE false) nil))))))

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

(deftype Handle [row]
  #?@(:clj [clojure.lang.IDeref
            (deref [_] (value row))]))

(defn row-of
  "The row behind a handle."
  [h] (if (instance? Handle h) (.-row ^Handle h) h))

(defn- linked? [e]
  (let [outs (g (g e rw/E-DEBTOR) rw/OUTS)
        i (gl e rw/E-IDX)]
    (and (< i (acount outs)) (identical? e (anth outs i)))))

(defn- new-comp! [w owner key at inputs body handles]
  (let [c (object-array rw/C-SIZE)]
    (s! c rw/TYPE rw/T-COMP)
    (s! c rw/ID (alloc-id! w))
    (s! c rw/WORLD w)
    (s! c rw/OUTS (alist))
    (s! c rw/REFS 0)
    (s! c rw/HOT 0)
    (s! c rw/HANDLES handles)
    (s! c rw/OWNER owner)
    (s! c rw/VERSION 0)
    (s! c rw/KEY key)
    (s! c rw/AT at)
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

(defn- find-created [l key]
  (when l
    (loop [i 0]
      (when (< i (acount l))
        (let [x (anth l i)]
          (if (== (long key) (gl x rw/KEY)) i (recur (inc i))))))))

(defn create-comp!
  "T3. `site` is a macro-time int, `inputs` the captured values."
  [site inputs body]
  (if-let [r (active-run)]
    (let [w (g r rw/R-WORLD)
          c (g r rw/R-OF)
          at (next-at! r)
          ords (or (g r rw/R-ORD) (let [m #?(:clj (java.util.HashMap.) :cljs (js/Map.))] (s! r rw/R-ORD m) m))
          ord (long (or #?(:clj (.get ^java.util.HashMap ords site) :cljs (.get ords site)) 0))
          _ #?(:clj (.put ^java.util.HashMap ords site (inc ord)) :cljs (.set ords site (inc ord)))
          key (bit-or (bit-shift-left (long site) 32) ord)
          basis (or (g c rw/C-BASIS) (let [l (alist)] (s! c rw/C-BASIS l) l))
          bi (find-created basis key)
          ab (g c rw/C-ADOPT)
          ai (when-not bi (find-created ab key))
          child (cond bi (anth basis bi)
                      ai (let [x (anth ab ai)]
                           (aput! ab ai (anth ab (dec (acount ab)))) (apop! ab)
                           (aadd! basis x)   ; the adoption reference moves to the basis
                           x))]
      (if child
        (do (s! child rw/AT at)   ; M3: adoption adds a (weak) handle (Z#13)
            (when-not (same-inputs? inputs (g child rw/C-INPUTS))
              ;; W#5: like a write to the rerun source.
              (s! child rw/C-INPUTS inputs)
              (s! child rw/C-BODY body)
              (if (g child rw/C-IDLE)
                (do (s! child rw/C-IDLE false) (s! child rw/C-VALIDITY nil)
                    (s! child rw/C-EPOCH (inc (gl child rw/C-EPOCH))))
                (do (s! child rw/C-EPOCH (inc (gl child rw/C-EPOCH)))
                    (s! child rw/C-RESTART true)
                    (mark-from! child)
                    (maybe-schedule! child))))
            (commit! w [:create-comp (g r rw/ID) site (g child rw/ID)])
            (->Handle child))
        ;; M3: a body creation starts with the body's (weak) handle (Z#13);
        ;; until weak handles exist it takes none.
        (let [child (new-comp! w c key at inputs body 0)]
          (aadd! basis child)
          (ref-inc! child)
          (commit! w [:create-comp (g r rw/ID) site (g child rw/ID)])
          (->Handle child))))
    (let [w (or *world* (throw (ex-info "no world: bind v2/*world*" {})))]
      (gated w
        (let [c (new-comp! w (g w rw/W-ROOT) 0 0 inputs body 1)]
          (aadd! (g w rw/W-RQ) c)   ; outside live: Rule R makes it idle (§3.4)
          (commit! w [:create-comp-top (g c rw/ID)])
          (drain! w)
          (->Handle c))))))

;; ---------------------------------------------------------------------------
;; Idle validation (§3.4, R#3)

(defn- validate!
  "Idle `c` becomes live with restart edges when every debtor in its
   validity still has the recorded version; otherwise it must run."
  [w c]
  (let [vs (g c rw/C-VALIDITY)
        ok? (and (not= :invalid vs)
                 (every? (fn [[d ver]]
                      (when (and (comp? d) (g d rw/C-IDLE)) (validate! w d))
                      (and (== (long ver) (gl d rw/VERSION))
                           (or (source? d) (live? d))))
                    vs))]
    (s! c rw/C-IDLE false)
    (s! c rw/C-VALIDITY nil)
    (if (and ok? (some? (g c rw/C-DONE-EPOCH)))
      (let [ins (g c rw/C-INS)]
        (doseq [[d ver at base] (when (sequential? vs) vs)]
          (let [e (link! w rw/EK-DEP c d at)]
            (s! e rw/E-SEEN ver)
            (s! e rw/E-BASE base)
            (aadd! ins e)))
        (s! c rw/C-DONE-EPOCH (g c rw/C-EPOCH)))
      (s! c rw/C-EPOCH (inc (gl c rw/C-EPOCH))))))

;; ---------------------------------------------------------------------------
;; Demand

(defn- demand!
  "Runs a demanded debtor that needs a run and is eligible (T6 demand)."
  [w d]
  (when (comp? d)
    (when (g d rw/C-IDLE) (validate! w d))
    (when (and (needs-run? d) (zero? (gl d rw/C-PENDING)))
      (dispatch! w d))))

;; ---------------------------------------------------------------------------
;; Rule R (§3.3) by retention counts

(defn- demote!
  "§3.3 step 1.3: a computation outside `live`."
  [w c]
  (when-let [r (g c rw/C-RUN)] (cancel-replace! w r))
  (let [ins (g c rw/C-INS)
        validity (loop [acc []]
                   (if (pos? (acount ins))
                     (let [e (apop! ins)
                           d (g e rw/E-DEBTOR)
                           acc (conj acc [d (g e rw/E-SEEN) (g e rw/E-AT) (g e rw/E-BASE)])]
                       (unlink! w e)
                       (recur acc))
                     acc))]
    (when-let [b (g c rw/C-BASIS)]
      (s! c rw/C-BASIS nil)
      (dotimes [i (acount b)] (ref-dec! (anth b i))))
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
        (let [row (apop! rq)]
          (when (zero? (gl row rw/REFS))
            (cond
              (comp? row)
              (do (when-not (g row rw/C-IDLE) (demote! w row))
                  (when (and (g row rw/C-IDLE) (zero? (gl row rw/HANDLES)))
                    (unregister! w row)))
              (source? row)
              (when (zero? (gl row rw/HANDLES)) (unregister! w row)))))
        (recur)))))

;; ---------------------------------------------------------------------------
;; Drain

(defn- resume! [w a]
  (let [r (g a rw/A-RUN)
        c (g r rw/R-OF)]
    (when (and (identical? a (g r rw/R-ACTV)) (current? c r) (== rw/ACT-PARKED (gl r rw/R-ACT)))
      (s! r rw/R-ACTV nil)
      (s! r rw/R-ACT rw/ACT-ACTIVE)
      (unregister! w a)
      (commit! w [:resume (g a rw/ID)])
      (let [[v err?] (let [^objects sl (g a rw/A-SLOTS)] (aget sl 0))
            k (g a rw/A-R) ek (g a rw/A-E)]
        (slice! r (if err? #(ek v) #(k v)))))))

(defn- drain! [w]
  (when-not (or (g w rw/W-DRAINING) (active-run))
    (s! w rw/W-DRAINING true)
    (try
      (let [ready (g w rw/W-READY)
            resume (g w rw/W-RESUME)]
        (loop []
          (cond
            (pos? (acount resume))
            (let [a (anth resume 0)]
              #?(:clj (.remove ^java.util.ArrayList resume (int 0)) :cljs (.shift resume))
              (resume! w a)
              (rule-r! w)
              (recur))
            (pos? (acount ready))
            (let [c (anth ready 0)]
              #?(:clj (.remove ^java.util.ArrayList ready (int 0)) :cljs (.shift ready))
              (s! c rw/C-QUEUED false)
              (when (and (hot? c) (zero? (gl c rw/C-PENDING)) (needs-run? c))
                (dispatch! w c))
              (rule-r! w)
              (recur))
            :else (rule-r! w))))
      (finally (s! w rw/W-DRAINING false)))
    (let [cbs (g w rw/W-CALLBACKS)]
      (when (pos? (acount cbs))
        (let [batch (acopy cbs)]
          (aclear! cbs)
          (dotimes [i (acount batch)]
            (let [[cb [v err?]] (anth batch i)] (cb v err?))))))))

;; ---------------------------------------------------------------------------
;; Host API


(defn- new-source! [w kind v owner key at]
  (let [x (object-array rw/X-SIZE)]
    (s! x rw/TYPE rw/T-SOURCE)
    (s! x rw/ID (alloc-id! w))
    (s! x rw/WORLD w)
    (s! x rw/OUTS (alist))
    (s! x rw/REFS 0)
    (s! x rw/HOT 0)
    (s! x rw/HANDLES 1)
    (s! x rw/OWNER owner)
    (s! x rw/VERSION 0)
    (s! x rw/KEY key)
    (s! x rw/AT at)
    (s! x rw/X-KIND kind)
    (s! x rw/X-VALUE v)
    (s! x rw/X-OPEN true)
    (register! w x)))

(defn signal
  "T1 at top level: a signal in `w` (default `*world*`)."
  ([v] (signal *world* v))
  ([w v]
   (gated w
     (let [x (new-source! w rw/SRC-SIGNAL v (g w rw/W-ROOT) 0 0)]
       (commit! w [:create-source-top (g (g w rw/W-ROOT) rw/ID) :signal (g x rw/ID)])
       (->Handle x)))))

(defn write!
  "T2: `version += 1`, fire dep edges and deliver observe edges (§4.5.1)."
  [h v]
  (let [x (row-of h)
        w (g x rw/WORLD)]
    (gated w
      (s! x rw/X-VALUE v)
      (s! x rw/VERSION (inc (gl x rw/VERSION)))
      (let [outs (acopy (g x rw/OUTS))]
        (dotimes [i (acount outs)]
          (let [e (anth outs i) k (gl e rw/E-KIND)]
            (cond (== k rw/EK-DEP) (fire-dep! w e)
                  (== k rw/EK-OBSERVE) (deliver-observe! w e)))))
      (commit! w [:write (g x rw/ID)])
      (drain! w))
    v))

(defn observe!
  "T8: `cb` receives (value err?) on each change. Returns an unobserve fn."
  [h cb]
  (let [d (row-of h)
        w (g d rw/WORLD)
        e (gated w
            (let [e (link! w rw/EK-OBSERVE cb d 0)]
              (when (and (comp? d) (g d rw/C-IDLE)) (validate! w d))
              (when (or (source? d) (live? d)) (deliver-observe! w e))
              (commit! w [:observe (g d rw/ID) (g e rw/ID)])
              (demand! w d)
              (drain! w)
              e))]
    (fn []
      (gated w
        (when (linked? e)
          (unlink! w e)
          (commit! w [:unobserve (g e rw/ID)])
          (drain! w))))))

(defn pin!
  "T20: a row is a root while its pin count is positive (Z#16)."
  [h]
  (let [x (row-of h) w (g x rw/WORLD)]
    (gated w
      (let [^java.util.Map pins (g w rw/W-PINS)
            n (long (or (.get pins x) 0))]
        (.put pins x (inc n))
        (ref-inc! x)
        (commit! w [:pin (g x rw/ID)])
        (drain! w)))
    h))

(defn unpin! [h]
  (let [x (row-of h) w (g x rw/WORLD)]
    (gated w
      (let [^java.util.Map pins (g w rw/W-PINS)
            n (long (or (.get pins x) 0))]
        (if (zero? n)
          (refuse! w [:unpin (g x rw/ID)])
          (do (if (== n 1) (.remove pins x) (.put pins x (dec n)))
              (ref-dec! x)
              (commit! w [:unpin (g x rw/ID)])
              (drain! w)))))
    h))

(defn release!
  "T19 by hand (weak handles arrive with M3)."
  [h]
  (let [x (row-of h) w (g x rw/WORLD)]
    (gated w
      (if (zero? (gl x rw/HANDLES))
        (refuse! w [:handle-drop (g x rw/ID)])
        (do (s! x rw/HANDLES (dec (gl x rw/HANDLES)))
            (when (zero? (gl x rw/REFS)) (aadd! (g w rw/W-RQ) x))
            (commit! w [:handle-drop (g x rw/ID)])
            (drain! w))))
    nil))

(defn value
  "Host read. A computation is demanded through a host wait edge for the
   duration of the read; M1 requires it to finish synchronously."
  [h]
  (let [d (row-of h)
        w (g d rw/WORLD)]
    (if (source? d)
      (g d rw/X-VALUE)
      (let [res (volatile! nil)]
        (gated w
          (let [e (link! w rw/EK-WAIT (fn [v err?] (vreset! res [v err?])) d 0)]
            (when (g d rw/C-IDLE) (validate! w d))
            (commit! w [:host-await (g d rw/ID) (g e rw/ID)])
            (if (live? d)
              (vreset! res (debtor-result d))
              (do (demand! w d) (drain! w)))
            (when (linked? e)
              (unlink! w e)
              (commit! w [:host-unawait (g e rw/ID)]))
            (drain! w)))
        (let [[v err?] (or @res (throw (ex-info "computation did not complete synchronously" {:id (g d rw/ID)})))]
          (if err? (throw v) v))))))

(defn track [_] (throw (ex-info "track outside a body" {})))
(defn await [_] (throw (ex-info "await outside a body" {})))

;; ---------------------------------------------------------------------------
;; Body macro (partial-cps)

#?(:clj
   (do
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-track [_ctx r e]
       (fn [[x]] `(track-effect! (row-of ~x) ~r ~e)))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-await [_ctx r e]
       (fn [[x]] `(await-effect! (row-of ~x) ~r ~e)))
     (def ^:private breakpoints
       {'org.replikativ.spindel.v2.core/track `bp-track
        'org.replikativ.spindel.v2.core/await `bp-await})
     (defmacro spin
       "A cached reactive computation (T3). Inside a body it is created in the
        running computation's basis and adopted by later runs."
       [& body]
       (let [r (gensym "r") e (gensym "e")
             params {:r r :e e :env &env :breakpoints breakpoints
                     :opaque-scopes #{`spin}}
             frees (vec (sort (free-vars/free-variables-or-all &env (cons 'do body))))
             site (bit-and 0x3fffffff (hash [(str *ns*) (:line (meta &form)) (:column (meta &form))]))]
         `(create-comp! ~site (object-array ~frees)
                        (fn [~r ~e] ~(ioc/invert params (cons 'do body))))))))
