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
            [is.simm.partial-cps.runtime :as pr]
            #?(:clj [is.simm.partial-cps.ioc :as ioc])
            #?(:clj [org.replikativ.spindel.engine.free-vars :as free-vars]))
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.rows :refer [g s! gl alist acount anth aadd! apop! aput! aclear! acopy]]
                            [org.replikativ.spindel.v2.core :refer [gated commit!]])))

#?(:clj (set! *warn-on-reflection* true))

(declare drain! demand! settle! pending-zero! rule-r! complete! validate!
         deliver-observe! value cancel! finish-task!)

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

(defn- new-scope [w id kind parent]
  (let [s (object-array rw/S-SIZE)]
    (s! s rw/TYPE rw/T-SCOPE)
    (s! s rw/ID id)
    (s! s rw/S-PARENT parent)
    (s! s rw/S-KIND kind)
    (s! s rw/S-OPEN true)
    (s! s rw/S-TASKS (alist))
    (s! s rw/S-CHILDREN (alist))
    (s! s rw/S-WORLD w)
    (when parent (aadd! (g parent rw/S-CHILDREN) s))
    (register! w s)))

(defn world
  "A new world. `:verify? true` keeps an id->row registry and a commit log
   (test only); `:hook` runs after every commit in verify mode."
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
     (s! w rw/W-START (alist))
     (s! w rw/W-CLEANUP (alist))
     (s! w rw/W-DRAINING false)
     (s! w rw/W-RQ (alist))
     (s! w rw/W-PINS #?(:clj (java.util.IdentityHashMap.) :cljs (js/Map.)))
     (s! w rw/W-CALLBACKS (alist))
     (when verify?
       (s! w rw/W-REG #?(:clj (java.util.LinkedHashMap.) :cljs (js/Map.)))
       (s! w rw/W-LOG (alist))
       (s! w rw/W-INTERN #?(:clj (java.util.HashMap.) :cljs (js/Map.)))
       (s! w rw/W-HOOK hook))
     (s! w rw/ID (alloc-id! w))
     (s! w rw/W-ROOT (new-scope w (alloc-id! w) :root nil))
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

(defn cancelled-ex
  "The error a cancelled entity's creditors and cleanup slices receive."
  [reason]
  (ex-info "cancelled" {:spindel/cancelled reason}))

(defn cancelled? [t] (some? (:spindel/cancelled (ex-data t))))

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
(defn- task? [row] (== rw/T-TASK (gl row rw/TYPE)))
(defn- source? [row] (== rw/T-SOURCE (gl row rw/TYPE)))
(defn- act? [row] (== rw/T-ACT (gl row rw/TYPE)))

(defn- live? [c]
  (and (not (g c rw/C-IDLE))
       (some? (g c rw/C-DONE-EPOCH))
       (== (gl c rw/C-DONE-EPOCH) (gl c rw/C-EPOCH))
       (zero? (gl c rw/C-PENDING))))

(defn- current? [c r]
  (and (some? r) (== (gl r rw/R-EPOCH) (gl c rw/C-EPOCH))))

(defn- run-current?
  "A task run is always current; a computation run iff its epoch matches."
  [r]
  (let [x (g r rw/R-OF)]
    (or (not (comp? x)) (current? x r))))

(defn- needs-run? [c]
  (and (not (g c rw/C-IDLE))
       (not (and (some? (g c rw/C-DONE-EPOCH))
                 (== (gl c rw/C-DONE-EPOCH) (gl c rw/C-EPOCH))))
       (not (current? c (g c rw/C-RUN)))))

(defn- deferred? [d] (and (source? d) (== rw/SRC-DEFERRED (gl d rw/X-KIND))))

(defn- final?
  "D1, for the kinds implemented so far."
  [d]
  (cond (task? d) (boolean (g d rw/K-DONE))
        (deferred? d) (pos? (gl d rw/VERSION))
        :else false))

(defn- settled?
  "A debtor whose result can be consumed now."
  [d]
  (cond (comp? d) (live? d)
        (task? d) (boolean (g d rw/K-DONE))
        (deferred? d) (pos? (gl d rw/VERSION))
        :else true))

(defn- hot? [row] (pos? (gl row rw/HOT)))

(declare blocked?)

(defn- eligible?
  "§4.5.7: every dirty computation debtor (a marked in-edge) has settled or
   is blocked."
  [c]
  (or (zero? (gl c rw/C-PENDING))
      (let [ins (g c rw/C-INS)]
        (loop [i 0]
          (if (< i (acount ins))
            (let [e (anth ins i)]
              (if (and (g e rw/E-MARKED) (not (blocked? (g e rw/E-DEBTOR) 0)))
                false
                (recur (inc i))))
            true)))))

(defn- blocked?
  "§4.5.6, the least predicate: the entity's current run is parked and every
   unfilled member's debtor is a source or a blocked entity. A cycle is not
   blocked (a user deadlock)."
  [x depth]
  (and (< (long depth) 64)
       (let [r (cond (comp? x) (let [r (g x rw/C-RUN)] (when (current? x r) r))
                     (task? x) (g x rw/K-RUN))]
         (and r (== rw/ACT-PARKED (gl r rw/R-ACT))
              (let [a (g r rw/R-ACTV)
                    ^objects ms (when a (g a rw/A-MEMBERS))]
                (and ms
                     (loop [i 0 any? false]
                       (if (< i (alength ms))
                         (if-let [e (aget ms i)]
                           (let [d (g e rw/E-DEBTOR)]
                             (if (or (source? d) (blocked? d (inc (long depth))))
                               (recur (inc i) true)
                               false))
                           (recur (inc i) any?))
                         any?))))))))

(defn- maybe-schedule!
  "§4.5.7: a hot needs-run computation that is eligible is queued for
   dispatch."
  [c]
  (when (and (needs-run? c) (hot? c) (not (g c rw/C-QUEUED)) (eligible? c))
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

(defn- linked? [e]
  (let [outs (g (g e rw/E-DEBTOR) rw/OUTS)
        i (gl e rw/E-IDX)]
    (and (< i (acount outs)) (identical? e (anth outs i)))))

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

(defn- remove-dep!
  "Removes a dep edge from its computation's INS (T10, D2), keeping the
   running run's cursor on the same next site."
  [w e]
  (when (linked? e)
  (let [c (g e rw/E-CRED)
        ins (g c rw/C-INS)
        i #?(:clj (.indexOf ^java.util.ArrayList ins e) :cljs (.indexOf ins e))]
    (when-not (neg? i)
      #?(:clj (.remove ^java.util.ArrayList ins (int i)) :cljs (.splice ins i 1))
      (when-let [r (g c rw/C-RUN)]
        (when (> (gl r rw/R-CURSOR) i) (s! r rw/R-CURSOR (dec (gl r rw/R-CURSOR))))))
    (unlink! w e))))

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
  (cond (comp? d) [(g d rw/C-RESULT) (boolean (g d rw/C-ERR))]
        (task? d) [(g d rw/K-RESULT) (boolean (g d rw/K-ERR))]
        :else [(g d rw/X-VALUE) false]))

(defn- act-done? [a]
  (or (zero? (gl a rw/A-REMAINING)) (some? (g a rw/A-WINNER))))

(defn- slot-fill!
  "Fills every slot whose member is `e` (Z#7). A complete activation that is
   not on the host stack is queued for resumption."
  [w a e res]
  (when-not (act-done? a)
    (let [^objects ms (g a rw/A-MEMBERS)
          ^objects sl (g a rw/A-SLOTS)
          n (alength ms)]
      (dotimes [i n]
        (when (identical? e (aget ms i))
          (aset ms i nil)
          (aset sl i res)
          (s! a rw/A-REMAINING (dec (gl a rw/A-REMAINING)))
          (when (and (= :any (g a rw/A-MODE)) (nil? (g a rw/A-WINNER)))
            (s! a rw/A-WINNER i))))
      (when (and (act-done? a) (not (g a rw/A-INLINE)))
        (aadd! (g w rw/W-RESUME) a)))))

(defn- fill!
  "T9 delivery into the activation `a` that dep edge `e` is an unfilled
   member of."
  [w e a]
  (let [r (g a rw/A-RUN)
        d (g e rw/E-DEBTOR)]
    (when (and (run-current? r) (== rw/ACT-PARKED (gl r rw/R-ACT)))   ; §4.5.4
      (s! e rw/E-ACT nil)
      (s! e rw/E-ARMED true)
      (s! e rw/E-SEEN (g d rw/VERSION))
      (slot-fill! w a e (debtor-result d)))))

(defn- fire-wait!
  "T9 on a wait edge: fills its activation's slot, or resolves the host
   promise; the edge is consumed (D2)."
  [w e]
  (let [cred (g e rw/E-CRED)
        d (g e rw/E-DEBTOR)
        res (debtor-result d)]
    (unlink! w e)
    (if (and (some? cred) (not (fn? cred)) (act? cred))
      (let [r (g cred rw/A-RUN)]
        (when (and (identical? cred (g r rw/R-ACTV)) (run-current? r)
                   (== rw/ACT-PARKED (gl r rw/R-ACT)))
          (slot-fill! w cred e res)))
      (aadd! (g w rw/W-CALLBACKS) [cred res]))))

(defn- fire-dep!
  "T9 on a dep edge whose debtor changed."
  [w e]
  (when (g e rw/E-ARMED)
    (let [a (g e rw/E-ACT)]
      (if (and a (run-current? (g a rw/A-RUN)))
        (fill! w e a)
        (invalidate! e)))))

(defn- settle!
  "§4.5.2: `d` became live (or final). Changed out-edges fire before they
   are unmarked; unfilled members of a current activation are delivered
   either way (Z#20). Wait edges are consumed."
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
          (== k rw/EK-WAIT) (fire-wait! w e))))
    ;; T10: dep edges on a final debtor are removed after their delivery.
    (when (final? d)
      (let [outs (acopy (g d rw/OUTS))]
        (dotimes [i (acount outs)]
          (let [e (anth outs i)]
            (when (and (== rw/EK-DEP (gl e rw/E-KIND)) (g e rw/E-ARMED) (nil? (g e rw/E-ACT)))
              (remove-dep! w e))))))))

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
    (when (and (settled? d) (or (nil? seen) (> (long ver) (long seen))))
      (s! e rw/E-SEEN ver)
      (aadd! (g w rw/W-CALLBACKS) [(g e rw/E-CRED) (debtor-result d)]))))

;; ---------------------------------------------------------------------------
;; Runs and scopes

(defn- new-run! [w x epoch]
  (let [r (object-array rw/R-SIZE)]
    (s! r rw/TYPE rw/T-RUN)
    (s! r rw/ID (alloc-id! w))
    (s! r rw/R-SCOPE (alloc-id! w))          ; run scope id; T4/T5/T11 order: run, scope
    (s! r rw/R-WORLD w)
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
  (or (g r rw/R-SROW)
      (let [x (g r rw/R-OF)
            owner (g x rw/OWNER)
            parent (when (and (task? x) owner (== rw/T-SCOPE (gl owner rw/TYPE))) owner)
            s (new-scope w (g r rw/R-SCOPE) :run parent)]
        (s! r rw/R-SROW s)
        s)))

(defn- remove-scope-if-empty!
  "T16/Z#18: a closed scope row goes once its subtree has no rows left."
  [w s]
  (when (and (not (g s rw/S-OPEN))
             (zero? (acount (g s rw/S-TASKS)))
             (zero? (acount (g s rw/S-CHILDREN))))
    (unregister! w s)
    (when-let [p (g s rw/S-PARENT)]
      (let [cs (g p rw/S-CHILDREN)
            i #?(:clj (.indexOf ^java.util.ArrayList cs s) :cljs (.indexOf cs s))]
        (when-not (neg? i) #?(:clj (.remove ^java.util.ArrayList cs (int i)) :cljs (.splice cs i 1)))
        (remove-scope-if-empty! w p)))))

(defn- close-scope!
  "T16: cancels the work owned by the subtree, closes its scopes."
  [w s]
  (when (g s rw/S-OPEN)
    (s! s rw/S-OPEN false)
    (let [ts (acopy (g s rw/S-TASKS))]
      (dotimes [i (acount ts)]
        (when-let [r (g (anth ts i) rw/K-RUN)] (cancel! w r ::cancelled))))
    (let [cs (acopy (g s rw/S-CHILDREN))]
      (dotimes [i (acount cs)] (close-scope! w (anth cs i)))))
  (remove-scope-if-empty! w s))

(defn- retire!
  "T13, in Z#18 order."
  [w r]
  (let [x (g r rw/R-OF)]
    (if (comp? x)
      (when (identical? r (g x rw/C-RUN)) (s! x rw/C-RUN nil))
      (when (identical? r (g x rw/K-RUN)) (s! x rw/K-RUN nil)))
    (when-let [s (g r rw/R-SROW)] (close-scope! w s))
    (unregister! w r)))

(defn- fins ^long [r] (let [n (g r rw/R-FINS)] (if n (long n) 0)))

(defn- retire-check!
  "T13: retired iff done, no slice, no finalizers, no resources."
  [w r]
  (when (and (== rw/ACT-DONE (gl r rw/R-ACT)) (not (g r rw/R-SLICE))
             (zero? (fins r)) (nil? (g r rw/R-RES)))
    (retire! w r)))

(defn- release-members!
  "An activation is removed: dep members stay with the computation (W#2),
   wait members are removed with it (D2)."
  [w a]
  (let [^objects ms (g a rw/A-MEMBERS)]
    (dotimes [i (alength ms)]
      (when-let [e (aget ms i)]
        (aset ms i nil)
        (if (== rw/EK-DEP (gl e rw/E-KIND))
          (s! e rw/E-ACT nil)
          (when (linked? e) (unlink! w e))))))
  (unregister! w a))

(defn- drop-activation! [w r]
  (when-let [a (g r rw/R-ACTV)]
    (s! r rw/R-ACTV nil)
    (release-members! w a)
    a))

(defn- cancel!
  "T14 `cancel(R)` (`reason` ::cancelled) or, with `replace? true`,
   `cancel(R, replace)` (Y#2). Runs hold no finalizers or resources yet
   (M2d/M3), so a run outside a slice retires at once."
  ([w r reason] (cancel! w r reason false))
  ([w r reason replace?]
   (when-not (== rw/ACT-DONE (gl r rw/R-ACT))
     (s! r rw/R-ACT rw/ACT-DONE)
     (s! r rw/R-MODE 1)
     ;; Finalizers (T14, B3): a parked run with open finally regions unwinds
     ;; in a cleanup slice through its activation's error continuation. A run
     ;; whose slice is on the stack unwinds at its next effect.
     (when-let [a (drop-activation! w r)]
       (when (pos? (fins r))
         (aadd! (g w rw/W-CLEANUP) [r (g a rw/A-E) (cancelled-ex reason)])))
     ;; children: runs owned by the run scope
     (when-let [s (g r rw/R-SROW)]
       (let [ts (acopy (g s rw/S-TASKS))]
         (dotimes [i (acount ts)]
           (when-let [cr (g (anth ts i) rw/K-RUN)] (cancel! w cr reason)))))
     (let [x (g r rw/R-OF)]
       (when (and (task? x) (not replace?))
         ;; debtor side (R#14): the task fails with ::cancelled
         (finish-task! w x (cancelled-ex reason) true)))
     (retire-check! w r))))

(defn- slice!
  "Runs `f` as a slice of `r` on the host stack, restoring the caller's
   active run afterwards (I10)."
  [r f]
  (let [prev (active-run)]
    (s! r rw/R-SLICE true)
    (set-active! r)
    (try
      (try (force! (f))
           (catch #?(:clj Throwable :cljs :default) t
             (complete! (or (active-run) r) t true)))
      (finally
        (s! r rw/R-SLICE false)
        (set-active! prev)
        (retire-check! (g r rw/R-WORLD) r)))))

(defn- ok-k [v] (complete! (active-run) v false))
(defn- err-k [t] (complete! (active-run) t true))

(defn- release-adoption! [w c]
  (when-let [ab (g c rw/C-ADOPT)]
    (s! c rw/C-ADOPT nil)
    (dotimes [i (acount ab)]
      (let [x (anth ab i)]
        ;; §5.2: a task the new run did not re-spawn is cancelled
        (when (and (task? x) (g x rw/K-RUN)) (cancel! w (g x rw/K-RUN) ::cancelled))
        (ref-dec! x))))
  (when-let [bs (g c rw/C-ADOPT-BASE)]
    (s! c rw/C-ADOPT-BASE nil)
    (dotimes [i (acount bs)] (ref-dec! (g (anth bs i) rw/E-DEBTOR)))))

(defn- finish-task!
  "Sets a task's result and fires its creditors; ownership retention ends."
  [w k v err?]
  (when-not (g k rw/K-DONE)
    (s! k rw/K-DONE true)
    (s! k rw/K-RESULT v)
    (s! k rw/K-ERR (boolean err?))
    (s! k rw/VERSION (inc (gl k rw/VERSION)))
    (settle! w k)
    (let [owner (g k rw/OWNER)]
      (when (and owner (not (fn? owner)) (== rw/T-SCOPE (gl owner rw/TYPE)))
        (let [ts (g owner rw/S-TASKS)
              i #?(:clj (.indexOf ^java.util.ArrayList ts k) :cljs (.indexOf ts k))]
          (when-not (neg? i)
            #?(:clj (.remove ^java.util.ArrayList ts (int i)) :cljs (.splice ts i 1))
            (ref-dec! k))
          (remove-scope-if-empty! w owner))))))

(defn- complete!
  "T12."
  [r v err?]
  (when (and r (== rw/ACT-ACTIVE (gl r rw/R-ACT)))
    (let [w (g r rw/R-WORLD)
          x (g r rw/R-OF)]
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
          (commit! w [:complete (g r rw/ID) (if err? :err :ok) [:opaque v]])
          (when (live? x) (settle! w x)))
        (do
          ;; Q10: children not awaited and not detached are cancelled
          (when-let [s (g r rw/R-SROW)]
            (let [ts (acopy (g s rw/S-TASKS))]
              (dotimes [i (acount ts)]
                (when-let [cr (g (anth ts i) rw/K-RUN)] (cancel! w cr ::cancelled)))))
          (finish-task! w x v err?)
          (commit! w [:complete (g r rw/ID) (if err? :err :ok) [:opaque v]])))))
  nil)

;; ---------------------------------------------------------------------------
;; Dispatch (T5, T11)

(defn- earliest-fired [c]
  (let [ins (g c rw/C-INS)]
    (loop [i 0]
      (when (< i (acount ins))
        (let [e (anth ins i)]
          (if (g e rw/E-ARMED) (recur (inc i)) i))))))

(defn- restore-ordinals! [c r]
  (when-let [basis (g c rw/C-BASIS)]
    (when (pos? (acount basis))
      (let [^java.util.Map ords #?(:clj (java.util.HashMap.) :cljs (js/Map.))]
        (dotimes [i (acount basis)]
          (let [key (gl (anth basis i) rw/KEY)
                site (bit-shift-right key 32)
                nxt (inc (bit-and key 0xffffffff))
                cur (long (or (.get ords site) 0))]
            (when (> nxt cur) #?(:clj (.put ords site nxt) :cljs (.set ords site nxt)))))
        (s! r rw/R-ORD ords)))))

(defn- dispatch!
  "T11 (and T5 for a computation without a fired edge): starts the
   computation's next run, re-entering at its earliest fired dep edge when
   that site is re-entrant (X#2)."
  [w c]
  (s! c rw/C-QUEUED false)
  (when (needs-run? c)
    (when-let [old (g c rw/C-RUN)] (cancel! w old ::cancelled true))
    (let [ins (g c rw/C-INS)
          restart? (g c rw/C-RESTART)
          ei (when-not restart? (earliest-fired c))
          e (when ei (anth ins ei))
          at (if e (gl e rw/E-AT) -1)]
      (s! c rw/C-RESTART false)
      ;; Suffix: dep edges after E keep their debtors through the adoption
      ;; baselines (§4.4, Z#21).
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
            (restore-ordinals! c r)
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
          ;; Restart from the body. E (if any) is re-armed; its baseline
          ;; advances when the new run reads it (Z#22).
          (do (when e (s! e rw/E-ARMED true))
              (slice! r #((g c rw/C-BODY) ok-k err-k))))))))

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
  (when (and (zero? (fins r)) (nil? (g r rw/R-RES))) k))

(defn enter-finally!
  "Body contract: a `finally` region opens (rewritten by the body macros)."
  []
  (when-let [r (active-run)] (s! r rw/R-FINS (inc (fins r)))))

(defn exit-finally!
  "A `finally` region closes; its block runs now."
  []
  (when-let [r (active-run)] (s! r rw/R-FINS (max 0 (dec (fins r))))))

(defn track-effect!
  "T7."
  [x k ek]
  (if-let [r (valid-run)]
    (let [w (g r rw/R-WORLD)
          c (g r rw/R-OF)
          at (next-at! r)]
      (if-not (comp? c)
        ;; Inside a task: a snapshot read with no edge (Q1, Z#19).
        (do (commit! w [:track (g r rw/ID) (g x rw/ID)])
            (k (iv/->Interval nil (g x rw/X-VALUE) nil)))
        (let [[e reused?] (site-edge! w r c x at (reentrant-k r k) ek)
              v (g x rw/X-VALUE)
              old (if reused?
                    (g e rw/E-BASE)
                    (when-let [b (adoption-baseline! c at x)] (g b rw/E-BASE)))]
          (s! e rw/E-BASE v)
          (s! e rw/E-SEEN (g x rw/VERSION))
          (s! e rw/E-ARMED true)
          (commit! w [:track (g r rw/ID) (g x rw/ID) (g e rw/ID)])
          (k (iv/->Interval old v nil)))))
    (unwind! ek)))

(defn- new-activation! [w aid r mode k ek ^objects members ^objects slots remaining]
  (let [a (object-array rw/A-SIZE)]
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
  (let [s (g r rw/R-SROW)]
    (dotimes [i (alength members)]
      (when-let [e (aget members i)]
        (let [d (g e rw/E-DEBTOR)]
          (when (and s (task? d) (identical? s (g d rw/OWNER))
                     (== 1 (acount (g d rw/OUTS))) (g d rw/K-RUN))
            (cancel! w (g d rw/K-RUN) ::cancelled)))))))

(defn- finish-activation!
  "Removes a complete activation and returns its delivery."
  [w r a]
  (s! r rw/R-ACTV nil)
  (s! r rw/R-ACT rw/ACT-ACTIVE)
  (when (and (= :any (g a rw/A-MODE)) (not (comp? (g r rw/R-OF))))
    (cancel-losers! w r (g a rw/A-MEMBERS)))
  (release-members! w a)
  (commit! w [:resume (g a rw/ID)])
  (group-result (g a rw/A-MODE) (g a rw/A-SLOTS) (g a rw/A-WINNER)))

(defn- notify-blocked!
  "§4.5.6-7: `x` parked. Creditors with a marked edge from it may now be
   eligible, and entities parked on it may now be blocked in turn."
  [x depth]
  (when (< (long depth) 64)
    (let [outs (g x rw/OUTS)]
      (dotimes [i (acount outs)]
        (let [e (anth outs i)
              k (gl e rw/E-KIND)]
          (cond
            (== k rw/EK-DEP)
            (let [c (g e rw/E-CRED)]
              (when (g e rw/E-MARKED) (maybe-schedule! c))
              (when (g e rw/E-ACT) (notify-blocked! c (inc (long depth)))))
            (== k rw/EK-WAIT)
            (let [a (g e rw/E-CRED)]
              (when (and (some? a) (not (fn? a)) (act? a))
                (notify-blocked! (g (g a rw/A-RUN) rw/R-OF) (inc (long depth)))))))))))

(defn- await-group!
  "T6: an activation over `ds` with `mode` (:one :all :any)."
  [ds mode k ek]
  (if-not (valid-run)
    (unwind! ek)
  (let [r (valid-run)]
    (let [w (g r rw/R-WORLD)
          x (g r rw/R-OF)
          at (next-at! r)
          aid (alloc-id! w)
          n (count ds)
          members (object-array n)
          slots (object-array n)
          in-comp? (comp? x)
          ;; group sites restart (Y#3); `one` sites re-enter when allowed (§2)
          kk (when (= mode :one) (reentrant-k r k))]
      ;; Member edges in debtor-list order; a repeated debtor shares its edge.
      (dotimes [i n]
        (let [d (row-of (nth ds i))
              prev (loop [j 0] (when (< j i)
                                 (let [m (aget members j)]
                                   (if (and m (identical? d (g m rw/E-DEBTOR))) m (recur (inc j))))))]
          (when (and (comp? d) (g d rw/C-IDLE)) (validate! w d))
          (cond
            prev (aset members i prev)
            in-comp? (let [[e _] (site-edge! w r x d at kk ek)]
                       (when (and (source? d) (not (deferred? d))) (s! e rw/E-BASE (g d rw/X-VALUE)))
                       (aset members i e))
            (and (source? d) (not (deferred? d))) nil       ; a task reads a signal once
            (settled? d) (alloc-id! w)                      ; consumed at once (Z#28)
            :else (aset members i (link! w rw/EK-WAIT nil d 0)))))
      ;; Fast path: settled members fill their slots in this commit.
      (let [remaining (volatile! n)
            winner (volatile! nil)]
        (dotimes [i n]
          (let [d (row-of (nth ds i))
                e (aget members i)]
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
              (when-let [e (aget members i)]
                (aset members i nil)
                (when (and (== rw/EK-WAIT (gl e rw/E-KIND)) (linked? e)) (unlink! w e))))
            (when in-comp?
              (doseq [d ds] (let [d (row-of d)]
                              (when (final? d)
                                (let [ins (g x rw/C-INS)]
                                  (dotimes [i (acount ins)]
                                    (let [e (anth ins i)]
                                      (when (and (identical? d (g e rw/E-DEBTOR)) (== at (gl e rw/E-AT)))
                                        (remove-dep! w e)))))))))
            (commit! w [:await (g r rw/ID) (mapv #(g (row-of %) rw/ID) ds) mode aid])
            (continue! (group-result mode slots @winner) k ek))
          (let [a (new-activation! w aid r mode k ek members slots @remaining)]
            (dotimes [i n]
              (when-let [e (aget members i)]
                (if (== rw/EK-DEP (gl e rw/E-KIND))
                  (s! e rw/E-ACT a)
                  (s! e rw/E-CRED a))))
            (park! r a)
            (commit! w [:await (g r rw/ID) (mapv #(g (row-of %) rw/ID) ds) mode aid])
            (notify-blocked! x 0)
            ;; Demanded debtors run on the host stack (I10).
            (dotimes [i n]
              (when-not (act-done? a)
                (demand! w (row-of (nth ds i)))))
            (if (and (act-done? a) (identical? a (g r rw/R-ACTV)) (run-current? r))
              (let [res (finish-activation! w r a)]
                (s! r rw/R-SLICE true)
                (set-active! r)
                (continue! res k ek))
              (do (s! a rw/A-INLINE false) nil)))))))))

(defn await-effect!
  "T6 with mode `one`."
  [d k ek]
  (await-group! [d] :one k ek))

(defn await-all-effect! [ds k ek] (await-group! (vec ds) :all k ek))
(defn await-any-effect! [ds k ek] (await-group! (vec ds) :any k ek))

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

(defn- debtor-row [w type size owner key at handles]
  (let [x (object-array size)]
    (s! x rw/TYPE type)
    (s! x rw/ID (alloc-id! w))
    (s! x rw/WORLD w)
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

(defn- find-created [l key]
  (when l
    (loop [i 0]
      (when (< i (acount l))
        (let [x (anth l i)]
          (if (== (long key) (gl x rw/KEY)) i (recur (inc i))))))))

(defn- creation-key! [r site]
  (let [^java.util.Map ords (or (g r rw/R-ORD) (let [m #?(:clj (java.util.HashMap.) :cljs (js/Map.))] (s! r rw/R-ORD m) m))
        ord (long (or (.get ords site) 0))]
    #?(:clj (.put ords site (inc ord)) :cljs (.set ords site (inc ord)))
    (bit-or (bit-shift-left (long site) 32) ord)))

(defn- adopt!
  "The creation of `c` with `key`, from its basis or its adoption basis."
  [c key]
  (let [basis (or (g c rw/C-BASIS) (let [l (alist)] (s! c rw/C-BASIS l) l))
        bi (find-created basis key)
        ab (g c rw/C-ADOPT)
        ai (when-not bi (find-created ab key))]
    (cond bi (anth basis bi)
          ai (let [x (anth ab ai)]
               (aput! ab ai (anth ab (dec (acount ab)))) (apop! ab)
               (aadd! basis x)   ; the adoption reference moves to the basis
               x))))

(defn create-comp!
  "T3. `site` is a macro-time int, `inputs` the captured values."
  [site inputs body]
  (if-let [r (active-run)]
    (when (valid-run)
      (let [w (g r rw/R-WORLD)
            c (g r rw/R-OF)
            at (next-at! r)]
        (if-not (comp? c)
          ;; Created by a task run: owned by the run scope, retained by demand.
          (let [child (new-comp! w (run-scope! w r) 0 at inputs body 0)]
            (aadd! (g w rw/W-RQ) child)
            (commit! w [:create-comp (g r rw/ID) site (g child rw/ID)])
            (->Handle child))
          (let [key (creation-key! r site)
                child (adopt! c key)]
            (if child
              (do (s! child rw/AT at)   ; M3: adoption adds a (weak) handle (Z#13)
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
                            (mark-from! child)
                            (maybe-schedule! child)))))
                  (commit! w [:create-comp (g r rw/ID) site (g child rw/ID)])
                  (->Handle child))
              ;; M3: a body creation starts with the body's (weak) handle
              ;; (Z#13); until weak handles exist it takes none.
              (let [child (new-comp! w c key at inputs body 0)]
                (aadd! (g c rw/C-BASIS) child)
                (ref-inc! child)
                (commit! w [:create-comp (g r rw/ID) site (g child rw/ID)])
                (->Handle child)))))))
    (let [w (or *world* (throw (ex-info "no world: bind v2/*world*" {})))]
      (gated w
        (let [c (new-comp! w (g w rw/W-ROOT) 0 0 inputs body 1)]
          (aadd! (g w rw/W-RQ) c)   ; outside live: Rule R makes it idle (§3.4)
          (commit! w [:create-comp-top (g c rw/ID)])
          (drain! w)
          (->Handle c))))))

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
      (let [w (g r rw/R-WORLD)
            x (g r rw/R-OF)
            at (next-at! r)]
        (if (comp? x)
          (let [key (creation-key! r site)
                old (adopt! x key)]
            (if (and old (task? old) (same-inputs? inputs (g old rw/K-INPUTS)))
              (do (s! old rw/AT at)
                  (commit! w [:spawn (g r rw/ID) site (g old rw/ID)])
                  (->Handle old))
              (do (when old                       ; changed captures: replace it
                    (let [basis (g x rw/C-BASIS)
                          i #?(:clj (.indexOf ^java.util.ArrayList basis old) :cljs (.indexOf basis old))]
                      #?(:clj (.remove ^java.util.ArrayList basis (int i)) :cljs (.splice basis i 1))
                      (when-let [or* (g old rw/K-RUN)] (cancel! w or* ::cancelled))
                      (ref-dec! old)))
                  (let [k (new-task! w x key at inputs body 0)]
                    (aadd! (g x rw/C-BASIS) k)
                    (ref-inc! k)
                    (start-task! w k)
                    (commit! w [:spawn (g r rw/ID) site (g k rw/ID)])
                    (->Handle k)))))
          (let [s (run-scope! w r)
                k (new-task! w s 0 at inputs body 0)]
            (aadd! (g s rw/S-TASKS) k)
            (ref-inc! k)
            (start-task! w k)
            (commit! w [:spawn (g r rw/ID) site (g k rw/ID)])
            (->Handle k)))))
    (let [w (or *world* (throw (ex-info "no world: bind v2/*world*" {})))]
      (gated w
        (let [s (g w rw/W-ROOT)
              k (new-task! w s 0 0 inputs body 1)]
          (aadd! (g s rw/S-TASKS) k)
          (ref-inc! k)
          (start-task! w k)
          (commit! w [:spawn-top (g k rw/ID)])
          (drain! w)
          (->Handle k))))))

;; ---------------------------------------------------------------------------
;; Idle validation (§3.4, R#3)

(defn- validate!
  "Idle `c` becomes live with restart edges when every debtor in its
   validity still has the recorded version (Z#24); otherwise it must run."
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
  (cond
    (comp? d)
    (do (when (g d rw/C-IDLE) (validate! w d))
        (when (and (needs-run? d) (eligible? d))
          (dispatch! w d)))
    (task? d) nil))

;; ---------------------------------------------------------------------------
;; Rule R (§3.3) by retention counts

(defn- demote!
  "§3.3 step 1.3: a computation outside `live`."
  [w c]
  (when-let [r (g c rw/C-RUN)] (cancel! w r ::cancelled true))
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
      (dotimes [i (acount b)]
        (let [x (anth b i)]
          (when (and (task? x) (g x rw/K-RUN)) (cancel! w (g x rw/K-RUN) ::cancelled))
          (ref-dec! x))))
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
              (task? row)
              (when (and (g row rw/K-DONE) (zero? (gl row rw/HANDLES)))
                (unregister! w row))
              (source? row)
              (when (zero? (gl row rw/HANDLES)) (unregister! w row)))))
        (recur)))))

;; ---------------------------------------------------------------------------
;; Drain

(defn- resume! [w a]
  (let [r (g a rw/A-RUN)]
    (when (and (identical? a (g r rw/R-ACTV)) (run-current? r) (== rw/ACT-PARKED (gl r rw/R-ACT)))
      (let [res (finish-activation! w r a)
            k (g a rw/A-R) ek (g a rw/A-E)]
        (slice! r #(continue! res k ek))))))

(defn- start! [w r]
  (when (== rw/ACT-ACTIVE (gl r rw/R-ACT))
    (let [k (g r rw/R-OF)]
      (commit! w [:start (g r rw/ID)])
      (slice! r #((g k rw/K-BODY) ok-k err-k)))))

(defn- pop-first! [l]
  (let [x (anth l 0)]
    #?(:clj (.remove ^java.util.ArrayList l (int 0)) :cljs (.shift l))
    x))

(defn- drain! [w]
  (when-not (or (g w rw/W-DRAINING) (active-run))
    (s! w rw/W-DRAINING true)
    (try
      (let [ready (g w rw/W-READY)
            resume (g w rw/W-RESUME)
            start (g w rw/W-START)]
        (loop []
          (cond
            (pos? (acount (g w rw/W-CLEANUP)))
            (let [[r ek ex] (pop-first! (g w rw/W-CLEANUP))]
              (commit! w [:finalize (g r rw/ID)])
              (slice! r #(ek ex))
              (rule-r! w)
              (recur))
            (pos? (acount start)) (do (start! w (pop-first! start)) (rule-r! w) (recur))
            (pos? (acount resume)) (do (resume! w (pop-first! resume)) (rule-r! w) (recur))
            (pos? (acount ready))
            (let [c (pop-first! ready)]
              (s! c rw/C-QUEUED false)
              (when (and (hot? c) (needs-run? c) (eligible? c))
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
  (let [x (debtor-row w rw/T-SOURCE rw/X-SIZE owner key at 1)]
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
       (commit! w [:create-source-top (g (g w rw/W-ROOT) rw/ID) :signal [:opaque v] (g x rw/ID)])
       (->Handle x)))))

(defn- mailbox? [x] (== rw/SRC-MAILBOX (gl x rw/X-KIND)))

(defn- deque ^java.util.ArrayDeque [x i] (g x i))

(defn- available? [x]
  (if (mailbox? x)
    (not (.isEmpty (deque x rw/X-VALUE)))
    (pos? (gl x rw/X-VALUE))))

(defn- consume! [x]
  (if (mailbox? x)
    (.pollFirst (deque x rw/X-VALUE))
    (do (s! x rw/X-VALUE (dec (gl x rw/X-VALUE))) true)))

(defn consume-effect!
  "`take!` (mailbox) or `acquire!` (semaphore): a consuming operation, always
   a wait edge, never a dependency (§4.3). Waiters are served FIFO."
  [x k ek]
  (if-let [r (valid-run)]
    (let [w (g r rw/R-WORLD)
          _ (next-at! r)
          aid (alloc-id! w)]
      (if (available? x)
        (let [v (consume! x)]
          (alloc-id! w)                             ; the consumed wait edge
          (s! x rw/VERSION (inc (gl x rw/VERSION)))
          (commit! w [:take (g r rw/ID) (g x rw/ID) aid])
          (k v))
        (let [members (object-array 1)
              a (new-activation! w aid r :one k ek members (object-array 1) 1)
              e (link! w rw/EK-WAIT a x 0)]
          (aset members 0 e)
          (.addLast (deque x rw/X-WAITERS) e)
          (park! r a)
          (s! a rw/A-INLINE false)
          (commit! w [:take (g r rw/ID) (g x rw/ID) aid])
          (notify-blocked! (g r rw/R-OF) 0)
          nil)))
    (unwind! ek)))

(defn- serve-waiter!
  "The first waiter whose activation can still receive, or nil. Waiters of
   stale or cancelled runs are skipped (§4.5.4)."
  [w x v]
  (let [q (deque x rw/X-WAITERS)]
    (loop []
      (when-let [e (.pollFirst q)]
        (let [a (g e rw/E-CRED)
              r (g a rw/A-RUN)]
          (if (and (linked? e) (identical? a (g r rw/R-ACTV)) (run-current? r)
                   (== rw/ACT-PARKED (gl r rw/R-ACT)))
            (do (unlink! w e)
                (slot-fill! w a e [v false])
                true)
            (recur)))))))

(defn mailbox
  "T1 at top level: a FIFO mailbox (§4.3)."
  ([] (mailbox *world*))
  ([w]
   (gated w
     (let [x (new-source! w rw/SRC-MAILBOX (java.util.ArrayDeque.) (g w rw/W-ROOT) 0 0)]
       (s! x rw/X-WAITERS (java.util.ArrayDeque.))
       (commit! w [:create-source-top (g (g w rw/W-ROOT) rw/ID) :mailbox [:opaque nil] (g x rw/ID)])
       (->Handle x)))))

(defn post!
  "Appends `v`, or hands it to the first waiter, atomically (§4.3)."
  [h v]
  (let [x (row-of h) w (g x rw/WORLD)]
    (gated w
      (s! x rw/VERSION (inc (gl x rw/VERSION)))
      (when-not (serve-waiter! w x v)
        (.addLast (deque x rw/X-VALUE) v))
      (commit! w [:post (g x rw/ID) [:opaque v]])
      (drain! w))
    nil))

(defn semaphore
  "T1 at top level: a counting semaphore with `n` permits (§4.3)."
  ([n] (semaphore *world* n))
  ([w n]
   (gated w
     (let [x (new-source! w rw/SRC-SEMAPHORE (long n) (g w rw/W-ROOT) 0 0)]
       (s! x rw/X-WAITERS (java.util.ArrayDeque.))
       (commit! w [:create-source-top (g (g w rw/W-ROOT) rw/ID) :semaphore [:opaque n] (g x rw/ID)])
       (->Handle x)))))

(defn sem-release!
  "Gives the permit to the first armed waiter, or returns it (§4.3)."
  [h]
  (let [x (row-of h) w (g x rw/WORLD)]
    (gated w
      (s! x rw/VERSION (inc (gl x rw/VERSION)))
      (when-not (serve-waiter! w x true)
        (s! x rw/X-VALUE (inc (gl x rw/X-VALUE))))
      (commit! w [:release (g x rw/ID)])
      (drain! w))
    nil))

(defn deferred
  "T1 at top level: a deferred, delivered once (§4.3)."
  ([] (deferred *world*))
  ([w]
   (gated w
     (let [x (new-source! w rw/SRC-DEFERRED nil (g w rw/W-ROOT) 0 0)]
       (commit! w [:create-source-top (g (g w rw/W-ROOT) rw/ID) :deferred [:opaque nil] (g x rw/ID)])
       (->Handle x)))))

(defn deliver!
  "Delivers a deferred once: fires its edges and finalizes it (§4.3, T10).
   A second delivery is refused."
  [h v]
  (let [x (row-of h)
        w (g x rw/WORLD)]
    (gated w
      (if (final? x)
        (refuse! w [:deliver (g x rw/ID) [:opaque v]])
        (do (s! x rw/X-VALUE v)
            (s! x rw/VERSION 1)
            (settle! w x)
            (commit! w [:deliver (g x rw/ID) [:opaque v]])
            (drain! w))))
    v))

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
      (commit! w [:write (g x rw/ID) [:opaque v]])
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
              (deliver-observe! w e)
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

(defn cancel-task!
  "T14 from the host on a task."
  [h]
  (let [k (row-of h) w (g k rw/WORLD)]
    (gated w
      (if-let [r (g k rw/K-RUN)]
        (do (cancel! w r ::cancelled)
            (commit! w [:cancel (g r rw/ID)])
            (drain! w))
        (refuse! w [:cancel (g k rw/ID)])))
    nil))

(defn value
  "Host read (T22). A computation or task is demanded through a host wait
   edge for the duration of the read; this requires it to finish within the
   drain (blocking host awaits arrive with ingress, M3)."
  [h]
  (let [d (row-of h)
        w (g d rw/WORLD)]
    (if (source? d)
      (g d rw/X-VALUE)
      (let [res (volatile! nil)]
        (gated w
          (let [e (link! w rw/EK-WAIT (fn [v err?] (vreset! res [v err?])) d 0)]
            (when (and (comp? d) (g d rw/C-IDLE)) (validate! w d))
            (commit! w [:host-await (g d rw/ID) (g e rw/ID)])
            (if (settled? d)
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
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-consume [_ctx r e]
       (fn [[x]] `(consume-effect! (row-of ~x) ~r ~e)))
     (def ^:private breakpoints
       {'org.replikativ.spindel.v2.core/track `bp-track
        'org.replikativ.spindel.v2.core/await `bp-await
        'org.replikativ.spindel.v2.core/await-all `bp-await-all
        'org.replikativ.spindel.v2.core/await-any `bp-await-any
        'org.replikativ.spindel.v2.core/take! `bp-consume
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
     (defn- register-finally
       "Body contract (§7): each literal `try` with a `finally` registers its
        region with the run, so cancellation can unwind through it (T14).
        Nested bodies and closures are left alone (they register their own)."
       [form]
       (cond
         (seq? form)
         (let [h (first form)]
           (cond
             (opaque-head? h) form
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
         `(fn [~r ~e] ~(ioc/invert params (register-finally (cons 'do body))))))
     (defn- site-of [form]
       (bit-and 0x3fffffff (hash [(str *ns*) (:line (meta form)) (:column (meta form))])))
     (defmacro spin
       "A cached reactive computation (T3). Inside a body it is created in the
        running computation's basis and adopted by later runs."
       [& body]
       (let [frees (vec (sort (free-vars/free-variables-or-all &env (cons 'do body))))]
         `(create-comp! ~(site-of &form) (object-array ~frees) ~(body-fn &env body))))
     (defmacro task
       "A task (T4): started at once; structured child of the creating run."
       [& body]
       (let [frees (vec (sort (free-vars/free-variables-or-all &env (cons 'do body))))]
         `(spawn! ~(site-of &form) (object-array ~frees) ~(body-fn &env body))))))
