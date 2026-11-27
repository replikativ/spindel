(ns org.replikativ.spindel.v2.core
  "Engine v2, layer 1 core (docs/engine-v2-spec.md).

   Scope so far: sources (signal, cell), computations, tasks with run scopes
   and structured cancellation, observe, pins, host waits, Rule R by
   retention counts.

   One world executes one slice at a time (D0). Every host entry takes the
   world gate, performs its transition, then drains: task starts,
   resumptions, eligible dispatches and Rule R, until nothing is left. Host
   callbacks run after the drain."
  (:refer-clojure :exclude [await atom])
  (:require [org.replikativ.spindel.v2.rows :as rw
             #?@(:clj [:refer [g gm s! gl alist acount anth aadd! apop! aput! aclear! acopy]])]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.incremental.deltaable :as dl]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.lifetime :as lt]
            [is.simm.partial-cps.runtime :as pr]
            #?(:clj [is.simm.partial-cps.ioc :as ioc])
            #?(:clj [org.replikativ.spindel.v2.macro-support :as ms])
            #?(:clj [org.replikativ.spindel.engine.free-vars :as free-vars]))
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.rows :refer [g gm s! gl alist acount anth aadd! apop! aput! aclear! acopy]]
                            [org.replikativ.spindel.v2.core :refer [gated commit! rv ingress-body]])))

#?(:clj (set! *warn-on-reflection* true))

(declare create-source-top-host! row-of world-of cancel-resource! resource-ack! demand! settle! pending-zero! rule-r! complete! validate!
         deliver-observe! value cancel! finish-task! request-atom-sweep! finish-metadata! maybe-finish-token!)

;; ---------------------------------------------------------------------------
;; Execution context: the world being processed and the run holding the slice
;; on this thread (B6: continuations close over no engine object; F1: rows
;; hold no pointer to a world, the world is the one being processed).

#?(:clj (def ^ThreadLocal ctx-tl (ThreadLocal.))
   ;; slot 3 (CLJS): the running slice's outer values of the vars it binds
   :cljs (def ctx-cell (doto (object-array 4) (aset 2 0))))

;; slot 3 (JVM): true while the thread runs no inline turns (D, H2)
(defn- ctx ^objects []
  #?(:clj (let [c (.get ctx-tl)]
            (if (nil? c) (let [c (object-array 4)] (aset c 2 (num 0)) (.set ctx-tl c) c) c))
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

;; test builds (rows/check-writes?): s! checks rows against this epoch
(vreset! rw/processed-epoch (fn [] (when-let [w (cw)] (aget ^objects w rw/W-EPOCH))))

;; Dynamic bindings belong to the run, not to the thread that runs a slice.
;; A run starts from its creator's frame (C-BIND, or the task's at spawn);
;; slice! installs R-BIND and saves the thread's frame back into it, so a
;; `binding` that spans an effect pushes and pops on the run's own frame
;; whichever thread runs each slice, and nothing leaks in or out. A fork
;; copies the run, hence its frame.
;;
;; CLJS has no thread frames: a frame is a map key -> [getter setter value]
;; of the vars the run binds (nil when none). A body `binding` adds entries
;; (push-bindings!), slice! sets the run's vars and restores the globals
;; after, reading the values back. Host-level bindings reach a creation only
;; for vars declared with `convey`.

#?(:cljs (def ^:private conveyed (volatile! {})))   ; key -> [getter setter]

(defn register-conveyed!
  "CLJS: host-level bindings of the var behind `getter`/`setter` reach the
   tasks and computations created under them (use the `convey` macro)."
  [k getter setter]
  #?(:cljs (vswap! conveyed assoc k [getter setter]))
  nil)

#?(:cljs
   (defn- read-back
     "Frame `m` with each var's current value (the run's vars are installed)."
     [m]
     (when m
       (persistent! (reduce-kv (fn [acc k [gt st]] (assoc! acc k [gt st (gt)])) (transient {}) m)))))

(defn- thread-frame
  "The binding frame a creation (or a fork of the running run) starts from."
  []
  #?(:clj (clojure.lang.Var/getThreadBindingFrame)
     :cljs (if-let [r (active-run)]
             (read-back (g r rw/R-BIND))
             (let [m @conveyed]
               (when (seq m) (reduce-kv (fn [acc k [gt st]] (assoc acc k [gt st (gt)])) {} m))))))

#?(:cljs
   (defn- install-bindings!
     "Sets frame `m`'s vars, recording their outer values in the slice table `t`."
     [m t]
     (reduce-kv (fn [_ k [gt st v]]
                  (when-not (contains? @t k) (vswap! t assoc k [st (gt)]))
                  (st v))
                nil m)))

(defn push-bindings!
  "CLJS body `binding` (B10): binds `entries` [[k getter setter value] ...]
   in the running run. Returns what `pop-bindings!` restores."
  [entries]
  #?(:clj (throw (ex-info "push-bindings! is CLJS only" {}))
     :cljs (let [r (active-run)
                 olds (mapv (fn [[_ gt]] (gt)) entries)
                 prev (when r (g r rw/R-BIND))]
             (when r
               (let [c (ctx)
                     t (or (aget c 3) (let [t (volatile! {})] (aset c 3 t) t))]
                 (doseq [[k gt st] entries]
                   (when-not (contains? @t k) (vswap! t assoc k [st (gt)]))))
               (s! r rw/R-BIND
                   (reduce (fn [m [k gt st v]] (assoc m k [gt st v])) (or prev {}) entries)))
             (doseq [[_ _ st v] entries] (st v))
             [(some? r) prev olds entries])))

(defn pop-bindings!
  "CLJS: leaves a body `binding` (push-bindings!)."
  [[in-run? prev olds entries]]
  #?(:cljs (do (dorun (map (fn [[_ _ st] o] (st o)) entries olds))
               (when in-run? (when-let [r (active-run)] (s! r rw/R-BIND prev)))))
  nil)

;; ---------------------------------------------------------------------------
;; World, ids, gate

(def ^:dynamic *world* nil)

(defn- report!
  "Reports `t` (`what` failed) on this thread. Never throws: a report is
   never part of a transition (an observer's or an isolated caller's throw
   cannot interrupt the engine through its report)."
  [what t]
  (try #?(:clj (binding [*out* *err*] (println what "failed:" t))
          :cljs (js/console.error what "failed:" t))
       (catch #?(:clj Throwable :cljs :default) _ nil))
  nil)

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

(defn- gone?
  "Whether Rule R already removed `row` (known only with the verification
   registry). After T21 revoked the handles, a finalizer may still hold one
   to a row nothing retains: its write, delivery, post, release or close
   (Z#40) reaches nobody and is not an item of the log."
  [w row]
  (when-let [reg (g w rw/W-REG)]
    (nil? (hs/mget reg (g row rw/ID)))))

(defn- new-scope [w id kind parent]
  (let [s (rw/new-row (g w rw/W-EPOCH) (g w rw/ID) rw/S-SIZE)]
    (s! s rw/TYPE rw/T-SCOPE)
    (s! s rw/ID id)
    (s! s rw/S-PARENT parent)
    (s! s rw/S-KIND kind)
    (s! s rw/S-WORLD (g w rw/W-FAMILY))     ; its world family (forks share it)
    (s! s rw/S-OPEN true)
    (s! s rw/S-TASKS (hs/oset))
    (s! s rw/S-CHILDREN (alist))
    (when parent (aadd! (gm parent rw/S-CHILDREN) s))
    (register! w s)))

;; A turn's time slice (H2). JS: 5 ms, so a long drain yields to paint and
;; input. JVM: none by default; the drainer runs on its own thread, and the
;; clock read per unit cost 2-7% in the quickbench graphs.
(def ^:private default-slice-ms #?(:clj nil :cljs 5))

(defn world
  "A new world. `:verify? true` keeps an id->row registry and a commit log
   (test only); `:hook` runs after every commit in verify mode. A turn ends
   after `:budget` units (items and slices) or, checked between units, once
   `:slice-ms` milliseconds have passed (H2; nil: no time slice; default
   5 on JS, none on the JVM)."
  ([] (world {}))
  ([{:keys [verify? hook inline? budget slice-ms executor]
     :or {inline? true budget 4096 slice-ms default-slice-ms}}]
   (let [w (rw/new-row nil nil rw/W-SIZE)
         next #?(:clj (java.util.concurrent.atomic.AtomicLong. 1)
                 :cljs (doto (long-array 1) (aset 0 1)))]
     (s! w rw/TYPE rw/T-WORLD)
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
     (s! w rw/W-SEALED (hs/flag false))
     (s! w rw/W-ADMITTING (hs/kids))
     (s! w rw/W-EXEC (or executor (hs/executor)))
     (s! w rw/W-INLINE (boolean inline?))
     (s! w rw/W-BUDGET (long budget))
     (s! w rw/W-SLICE (hs/ms->ticks slice-ms))
     (s! w rw/W-ROOTS (hs/lmap))
     (s! w rw/W-RELEASED false)
     (s! w rw/W-UNBORN false)
     (s! w rw/W-AFTER (alist))
     (s! w rw/W-STATE {})
     (s! w rw/W-ATOMS {})
     (s! w rw/W-FAMILY (lt/family))
     (s! w rw/W-WATCHES (lt/index))
     (s! w rw/W-SWEEP-GEN 0)
     (s! w rw/W-SWEEP-PENDING (hs/flag false))
     (s! w rw/W-META-CLOSED false)
     (s! w rw/W-RUNS 0)                       ; C1 W1; kids, subscriptions and the
     (s! w rw/W-COMPLETE false)               ; outstanding set are made on first use
     (when verify?
       (s! w rw/W-REG (hs/lmap))
       (s! w rw/W-LOG (alist))
       (s! w rw/W-INTERN #?(:clj (let [n (long-array 1)] (aset n 0 2)   ; reserved: 1 ::cancelled, 2 ::closed
                                      [(doto (java.util.HashMap.) (.put ::cancelled 1) (.put ::closed 2)) (java.util.WeakHashMap.) n])
                            :cljs nil))
       (s! w rw/W-HOOK hook))
     (s! w rw/ID (alloc-id! w))
     (s! w rw/W-EPOCH (rw/epoch (g w rw/ID) 0))
     (s! w rw/W-ROOT (new-scope w (alloc-id! w) :root nil))
     (lt/register-world! (g w rw/W-FAMILY) w (g w rw/ID) (g w rw/W-WATCHES) 0 request-atom-sweep!)
     w)))

(declare handoff!)

(defn- atom-maintenance!
  "Metadata only: no ingress, dormant activation, engine drain or callbacks.
   Like every holder of the gate, it hands off after releasing it (H2)."
  [w]
  (let [lk (g w rw/W-LOCK)]
    (if (hs/try-lock! lk)
      (do
        (try
          ;; Reset before reading generation/scanning: a new request now queues
          ;; a second pass, while a request before reset is covered by this one.
          (hs/flag-set! (g w rw/W-SWEEP-PENDING) false)
          (let [generation (lt/generation (g w rw/W-FAMILY))]
            (when-not (g w rw/W-META-CLOSED)
              (s! w rw/W-ATOMS
                  (persistent!
                   (reduce-kv (fn [m id entry]
                                (if (hs/deref-weak (first entry)) (assoc! m id entry) m))
                              (transient {}) (g w rw/W-ATOMS)))))
            (s! w rw/W-SWEEP-GEN generation))
          (finally (hs/unlock! lk)))
        (handoff! w))
      ;; A busy gate cannot lose the pending request. The dedicated scheduler
      ;; is asynchronous even when the world's application executor is inline.
      (hs/metadata-later! #(atom-maintenance! w) 1))))

(defn- request-atom-sweep! [w]
  (when (and (not (g w rw/W-META-CLOSED))
             (hs/flag-cas! (g w rw/W-SWEEP-PENDING) false true))
    (try (hs/metadata-later! #(atom-maintenance! w))
         (catch #?(:clj Throwable :cljs :default) t
           ;; nothing was scheduled: a later request must not find it pending
           (hs/flag-set! (g w rw/W-SWEEP-PENDING) false)
           (throw t)))))

(declare host!)

#?(:clj
   (defmacro gated
     "H1: runs `body` as a host item of world `w`: directly when this thread
      already holds the world (a slice or a callback), else enqueued and
      processed per H2. Returns the body's value when it ran before return."
     [w & body]
     `(host! ~w (fn [] ~@body))))

(defn- control-ex
  "An engine control signal (cancelled, closed, released, forked, unborn):
   an ExceptionInfo without a stack trace on the JVM. It is a signal, not a
   fault, and the engine makes one per affected entity: a trace each cost
   ~1.5 KB per retained row (foerster: ~150 MB)."
  [msg data]
  #?(:clj (proxy [clojure.lang.ExceptionInfo] [msg data] (fillInStackTrace [] this))
     :cljs (ex-info msg data)))

(defn cancelled-ex
  "The error a cancelled entity's creditors and cleanup slices receive."
  [reason]
  (control-ex "cancelled" {:spindel/cancelled reason}))

(defn cancelled? [t] (some? (:spindel/cancelled (ex-data t))))

(defn closed-ex
  "The error a waiter on a closed source without a value receives (Z#53)."
  []
  (control-ex "source closed" {:spindel/closed true}))

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
                  (let [c# (resolve-row ~ww ~r)] (when-not (identical? c# ~r) (aput! l# ~i c#)) c#)))
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

(declare lineage-ex copy-containers!)

;; --- MVCC fork tokens (v2-fork-memory-design §2.1, §2.6, §7) ----------------
;; A fork's token holds a cell `[ordinal state rows owner]`, also listed (in
;; ordinal order) by the owner: state :live, :shared or :dead; `rows` are
;; the owner's rows that saved a version this fork reads (newest live fork in
;; the version's range); `owner` is the owner world, weakly. A cell dies when
;; its token is collected (Cleaner) or its fork finishes unshared; then the
;; owner prunes exactly those rows, re-listing versions other forks still read.

(declare internal!)

(defn- cell-ordinal ^long [^objects c] (long (aget c 0)))
(defn- cell-live? [^objects c] (not (identical? :dead (aget c 1))))

(defn- first-at-least
  "Index of the first cell in `l` with ordinal >= a."
  ^long [l ^long a]
  (loop [lo 0 hi (acount l)]
    (if (< lo hi)
      (let [mid (quot (+ lo hi) 2)]
        (if (< (cell-ordinal (anth l mid)) a) (recur (inc mid) hi) (recur lo mid)))
      lo)))

(defn- live-token-in?
  "Whether a fork of `w` with an ordinal in [a, b] is still alive."
  [w ^long a ^long b]
  (when-let [l (g w rw/W-TOKENS)]
    (when (<= a b)
      (loop [i (first-at-least l a)]
        (when (< i (acount l))
          (let [c (anth l i)]
            (when (<= (cell-ordinal c) b)
              (if (cell-live? c) true (recur (inc i))))))))))

(defn- newest-live-cell
  "The cell of the newest live fork of `w` with an ordinal in [a, b]."
  [w ^long a ^long b]
  (when-let [l (g w rw/W-TOKENS)]
    (when (<= a b)
      (loop [i (dec (first-at-least l (inc b)))]
        (when (>= i 0)
          (let [c (anth l i)]
            (when (>= (cell-ordinal c) a)
              (if (cell-live? c) c (recur (dec i))))))))))

(defn- list-row! [^objects c r]
  (aadd! (or (aget c 2) (let [l (alist)] (aset c 2 l) l)) r))

(defn- prune-versions
  "The entries of version vector `vs` some live fork of `w` can still read."
  [w vs]
  (when vs
    (not-empty (filterv (fn [[k m]] (live-token-in? w k m)) vs))))

(defn- prune-cell!
  "A fork of `w` ended: prune the versions of the rows it listed; a version
   another live fork still reads is listed on that fork's cell. Dead cells
   leave the owner's list."
  [w ^objects c]
  (let [rows (aget c 2)]
    (aset c 2 nil)
    (when rows
      (dotimes [i (acount rows)]
        (let [^objects r (anth rows i)
              keep (rw/locking-row r
                                   (let [vs (prune-versions w (rw/versions r))]
                                     (rw/set-versions! r vs)
                                     vs))]
          (doseq [[k m] keep]
            (when-let [c2 (newest-live-cell w k m)] (list-row! c2 r)))))))
  (when-let [l (g w rw/W-TOKENS)]
    (loop [i (dec (acount l))]
      (when-not (neg? i)
        (when-not (cell-live? (anth l i)) (hs/remove-at! l i))
        (recur (dec i))))))

(defn- prune-later!
  "Prunes cell `c` of `w` under its gate, on the metadata thread: never an
   ingress item, so it is not work (W6, L12) and no quiescence check sees it.
   A busy gate retries later, as the other metadata jobs."
  [w c]
  (let [lk (g w rw/W-LOCK)]
    (if (hs/try-lock! lk)
      (do (let [prev (enter-world! w)]
            (try (prune-cell! w c) (finally (hs/unlock! lk) (leave-world! prev))))
          (handoff! w))
      (hs/metadata-later! #(prune-later! w c) 1))))

(defn- cell-ended!
  "Cell `c` is dead: its owner prunes, off the calling thread (a Cleaner
   thread, or the finishing fork's)."
  [^objects c]
  (when-let [w (hs/deref-weak (aget c 3))]
    (hs/metadata-later! #(prune-later! w c))))

(defn- register-token!
  "A fork of `w` at ordinal `o`: its token and cell."
  [w ^long o]
  (let [c (doto (object-array 4) (aset 0 #?(:clj (Long/valueOf o) :cljs o)) (aset 1 :live) (aset 3 (hs/weak w)))
        t (rw/token o c)
        l (or (g w rw/W-TOKENS) (let [l (alist)] (s! w rw/W-TOKENS l) l))]
    (aadd! l c)
    ;; the action holds the cell weakly: as a GC root it must not keep the
    ;; owner's rows (and through them the owner and its forks) reachable; while
    ;; the owner lives, its list keeps the cell
    (let [wc (hs/weak c)]
      (hs/on-collect! t (fn [] (when-let [^objects c (hs/deref-weak wc)] (aset c 1 :dead) (cell-ended! c)))))
    t))

(defn- own-token
  "The token world `w` got when it was forked (nil for a root)."
  [w]
  (nth (first (g w rw/W-LINEAGE)) 3 nil))

(defn- share-token!
  "Something is derived from `w` (a fork, an instance): its token is shared
   with the derived world's lineage and ends only when unreachable."
  [w]
  (when-let [t (own-token w)] (rw/token-share! t)))

(defn- finish-token!
  "`w` has finished: released, with no work, cleanup or armed resource left.
   Its token ends now unless shared, and the owner prunes its versions."
  [w]
  (when-let [t (own-token w)]
    (when (rw/token-finish! t) (cell-ended! (rw/token-cell t)))))

;; --- owner side -------------------------------------------------------------

(defn- image
  "An immutable version of row `r`: a clone with its own containers, no
   versions, no handle reference."
  [^objects r]
  (let [c (aclone r)]
    (copy-containers! c)
    (rw/set-versions! c nil)
    c))

;; A clone made for one reader only (`version-of` of an unchanged row): marked
;; by an identity sentinel in its versions slot, so `own-copy!` can take it
;; over instead of cloning it again.
(def ^:private fresh-mark (object-array 0))

(defn- fresh-image [^objects r]
  (let [c (image r)] (rw/set-versions! c fresh-mark) c))

(defn- preserve!
  "§2.3: `w` owns `r`, stamped with an older epoch of `w`. If a fork that may
   read `r` is alive, the row's current state becomes a version for the forks
   since its stamp, listed on the newest such fork's cell; then `r` is
   restamped and returned, mutable in place."
  [w ^objects r]
  (let [cur (g w rw/W-EPOCH)
        s (rw/epoch-ordinal (rw/stamp r))
        m (dec (rw/epoch-ordinal cur))
        c (newest-live-cell w s m)]
    (rw/locking-row r
                    (let [before (rw/versions r)
                          kept (when before (prune-versions w before))]
                      (rw/set-versions! r (if c (conj (or kept []) [s m (image r)]) kept)))
                    (aset r (unchecked-dec-int (alength r)) cur))
    (when c (list-row! c r))
    r))

;; --- fork side --------------------------------------------------------------

(defn- version-of
  "Row `x`'s state as seen by forks of its owner at ordinal `f`: a clone of
   the live row if it has not changed since, else its saved version. Never
   the live row itself."
  [^objects x ^long f]
  (rw/locking-row x
                  (if (<= (rw/epoch-ordinal (rw/stamp x)) f)
                    (fresh-image x)
                    (or (some (fn [[k m v]] (when (<= (long k) f (long m)) v)) (rw/versions x))
                        (throw (ex-info "MVCC: no version for a live fork" {:id (aget x rw/ID) :ordinal f}))))))

(defn- view
  "§2.4: the version of `r` this world sees, through its lineage (nearest
   first): an ancestor's copy as it was at the fork, or the ancestor's own row."
  [w ^objects r]
  (let [id (aget r rw/ID)
        owner (rw/epoch-world (rw/stamp r))]
    (loop [l (g w rw/W-LINEAGE)]
      (if-let [[a _cut f _tok m] (first l)]
        (if-let [x (get m id)]
          (version-of x f)
          (if (= owner a) (version-of r f) (recur (rest l))))
        (throw (lineage-ex r))))))

(defn resolve-row
  "This world's own row for reference `r` (the `rv` slow path): an owned row
   stamped by an older epoch is preserved and restamped (MVCC, §2.3); an
   inherited row is copied into this world from the version it sees (§2.4)."
  [w r]
  (let [^objects r r]
    (if (= (rw/epoch-world (rw/stamp r)) (g w rw/ID))
      (preserve! w r)
      (if-let [c (get (g w rw/W-FWD) (aget r rw/ID))]
        (if (identical? (rw/stamp c) (g w rw/W-EPOCH)) c (preserve! w c))
        (own-copy! w r (view w r))))))

(defn- peek-row
  "Read-only view of row `r` in `w`, without copying it: `r` when `w` owns it,
   its own copy, else the version it sees. Never written through; a write
   needs `rv`."
  [w r]
  (let [^objects r r]
    (if (= (rw/epoch-world (rw/stamp r)) (g w rw/ID))
      r
      (or (get (g w rw/W-FWD) (aget r rw/ID)) (view w r)))))

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
                      (when (<= rw/SRC-MAILBOX (long (aget c rw/X-KIND)) rw/SRC-SEMAPHORE)
                        (when-let [q (aget c rw/X-WAITERS)] (aset c rw/X-WAITERS (hs/dcopy q)))))
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
  "Copies version `v` of the inherited row `r` into world `w`: stamps the
   epoch, copies its containers, records it in the copy map (and the verify
   registry)."
  [w ^objects r ^objects v]
  (let [fresh? (identical? fresh-mark (rw/versions v))
        c (if fresh? v (aclone v))]
    (aset c (unchecked-dec-int (alength c)) (aget ^objects w rw/W-EPOCH))
    (rw/set-versions! c nil)
    (when-not fresh? (copy-containers! c))
    ;; F1: a resource's physical controller (timer, thread, external
    ;; callbacks) belongs to the world that set it; a copy elsewhere drops it
    (when (and (== rw/T-RES (long (aget c rw/TYPE)))
               (not= (aget c rw/Z-ORIGIN) (aget ^objects w rw/ID)))
      (aset c rw/Z-CTL nil))
    (aset ^objects w rw/W-FWD (assoc (aget ^objects w rw/W-FWD) (aget c rw/ID) c))
    ;; L12: a mergeable fork keeps, for every source it inherited and
    ;; touches, the identity its parent resolves, its version number and its
    ;; value at the fork (C2: the resolver's base; a frozen fork's first copy
    ;; of a row precedes its first change, so it is the fork-time state)
    (when-let [mb (aget ^objects w rw/W-MBASE)]
      (when (and (== rw/T-SOURCE (long (aget c rw/TYPE)))
                 (not= rw/SRC-LINK (long (aget c rw/X-KIND)))   ; a fork realizes its own (C0)
                 (< (long (aget c rw/ID)) (long (aget ^objects w rw/ID)))
                 (nil? (get mb (aget c rw/ID))))
        (aset ^objects w rw/W-MBASE (assoc mb (aget c rw/ID) [r (gl v rw/VERSION) (aget v rw/X-VALUE)]))))
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
  "Verify mode: the Nat for an opaque value. Collections intern structurally
   by their members' Nats, never by retaining the members themselves. Identity
   objects (fns, arrays, handles) are held weakly (census)."
  [w x]
  #?(:clj (if (nil? x)
            0
            (let [[^java.util.Map strong ^java.util.Map weak ^longs n] (g w rw/W-INTERN)
                  x (cond (cancelled? x) ::cancelled          ; reserved: 1 (see world)
                          (:spindel/closed (ex-data x)) ::closed   ; reserved: 2
                          :else x)
                  identity? (by-identity? x)
                  ;; A collection may contain handles, closures or metadata
                  ;; holding either. Keep only its shape and interned members.
                  ;; Lists and vectors compare equally; maps and sets do not.
                  k (if identity?
                      x
                      (cond
                        (map? x) [:map (into {} (map (fn [[k v]] [(intern-opaque! w k) (intern-opaque! w v)])) x)]
                        (set? x) [:set (into #{} (map #(intern-opaque! w %)) x)]
                        (coll? x) [:seq (mapv #(intern-opaque! w %) x)]
                        :else x))
                  ^java.util.Map m (if identity? weak strong)]
              (or (.get m k)
                  (let [v (aset n 0 (inc (aget n 0)))] (.put m k v) v))))
     :cljs 0))

(defn- opaque-item [w x]
  (cond (and (vector? x) (= :opaque (first x)) (== 2 (count x))) (intern-opaque! w (second x))
        ;; captures: element-wise, so equal captures (§1.6) give equal vectors
        (and (vector? x) (= :opaque-seq (first x)) (== 2 (count x)))
        (mapv #(intern-opaque! w %) (second x))
        (vector? x) (mapv #(opaque-item w %) x)
        :else x))

(defn- log-accept!
  "Verify mode: appends the accepted entry for `item0`; returns the logged
   item (the observer's argument)."
  [w item0]
  (let [item (opaque-item w item0)]
    (aadd! (g w rw/W-LOG) {:item item :accepted true})
    item))

(defn- observe-commit!
  "Verify mode: the commit observer (`W-HOOK`) on the logged `item` (nil:
   nothing logged), once the transition is complete. It is isolated: its
   throw is reported (`report!`) and never interrupts the transition."
  [w item]
  (when item
    (when-let [hook (g w rw/W-HOOK)]
      (try (hook w item)
           (catch #?(:clj Throwable :cljs :default) t (report! "commit observer" t)))))
  nil)

(defn log-commit!
  "Verify mode, at the end of a transition: the accepted entry, then the
   commit observer (`observe-commit!`)."
  [w item0]
  (observe-commit! w (log-accept! w item0)))

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
    (aadd! log {:item (opaque-item w item) :accepted false}))
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

(defn- deferred?
  "A source delivered once: a deferred or a link (C0)."
  [d]
  (and (source? d) (let [k (gl d rw/X-KIND)] (or (== k rw/SRC-DEFERRED) (== k rw/SRC-LINK)))))
(defn- link? [d] (and (source? d) (== rw/SRC-LINK (gl d rw/X-KIND))))
(defn- stream? [d] (and (source? d) (== rw/SRC-STREAM (gl d rw/X-KIND))))

;; A link's memoized error (C0 Q1): every reader of the position gets it.
(deftype Failure [err])
(defn- failure-err [^Failure f] (.-err f))
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

(defn- parked-members
  "The member edges of `x`'s current run when it is parked, else nil."
  [w x]
  (let [r (cond (comp? x) (let [r (rv w (g x rw/C-RUN))] (when (current? x r) r))
                (task? x) (rv w (g x rw/K-RUN)))]
    (when (and r (== rw/ACT-PARKED (gl r rw/R-ACT)))
      (when-let [a (rv w (g r rw/R-ACTV))] (g a rw/A-MEMBERS)))))

(defn- blocked-walk?
  "§4.5.6 exactly, without recursion: a depth-first walk keeping a result per
   entity. An entity met while still on the walk closes a cycle; it is not
   derivable, nor is anything that needs it (all members must be blocked)."
  [w x0]
  (let [memo (volatile! {})                       ; id -> true, false or :open
        frame (fn [x] (vswap! memo assoc (g x rw/ID) :open)
                (object-array [x (parked-members w x) 0 false]))]
    (loop [stack [(frame x0)]]
      (let [^objects f (peek stack)
            x (aget f 0) ^objects ms (aget f 1) i (long (aget f 2))]
        (if (and ms (< i (alength ms)))
          (let [e (rv w (aget ms i))
                d (when e (rv w (g e rw/E-DEBTOR)))
                known (when (and d (not (source? d)) (not (res? d))) (get @memo (g d rw/ID) ::none))]
            (cond
              (nil? e) (do (aset f 2 (inc i)) (recur stack))
              (or (source? d) (res? d) (true? known)) (do (aset f 2 (inc i)) (aset f 3 true) (recur stack))
              (= ::none known) (recur (conj stack (frame d)))   ; resumes at i with d's result
              :else (do (aset f 1 nil) (aset f 3 false) (recur stack))))   ; false or a cycle
          ;; done: blocked iff it had members and all were blocked
          (let [ok (boolean (and ms (aget f 3)))
                stack (pop stack)]
            (vswap! memo assoc (g x rw/ID) ok)
            (if (empty? stack)
              ok
              (let [^objects p (peek stack)]
                (if ok
                  (do (aset p 2 (inc (long (aget p 2)))) (aset p 3 true))
                  (do (aset p 1 nil) (aset p 3 false)))
                (recur stack)))))))))

(defn- blocked?
  "§4.5.6, the least predicate: the entity's current run is parked and every
   unfilled member's debtor is a source or a blocked entity. A cycle is not
   blocked (a user deadlock). Shallow chains recurse without allocating;
   from depth 64 on, the exact walk takes over (no depth bound, no deep
   stack)."
  [w x depth]
  (if (>= (long depth) 64)
    (blocked-walk? w x)
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
  (let [e (rw/new-row (g w rw/W-EPOCH) (g w rw/ID) rw/E-SIZE)
        outs (gm debtor rw/OUTS)]
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
        outs (gm debtor rw/OUTS)
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
          ins (gm c rw/C-INS)
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
        (instance? Failure (g d rw/X-VALUE)) [(failure-err (g d rw/X-VALUE)) true]
        (g d rw/X-OPEN) [(g d rw/X-VALUE) false]
        ;; Z#53: a closed source keeps a signal's or cell's value and a
        ;; delivered deferred's; a mailbox, a semaphore or an undelivered
        ;; deferred has none, so its waiters get an error
        (let [kind (gl d rw/X-KIND)]
          (or (== kind rw/SRC-MAILBOX) (== kind rw/SRC-SEMAPHORE)
              (and (or (== kind rw/SRC-DEFERRED) (== kind rw/SRC-LINK)) (zero? (gl d rw/VERSION)))))
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
    (let [^objects ms (gm a rw/A-MEMBERS)
          ^objects sl (gm a rw/A-SLOTS)
          n (alength ms)]
      (dotimes [i n]
        (when (identical? e (rv w (aget ms i)))
          (aset ms i nil)
          (aset sl i res)
          (s! a rw/A-REMAINING (dec (gl a rw/A-REMAINING)))
          ;; any: the first fill wins; all: the first err ends it (Z#61)
          (when (and (nil? (g a rw/A-WINNER))
                     (or (= :any (g a rw/A-MODE)) (and (= :all (g a rw/A-MODE)) (nth res 1))))
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
    ;; this world's copy: a pointer inherited from a fork's basis must not be
    ;; filled in place (the other world shares that row)
    (let [a (rv w (g e rw/E-ACT))]
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
            (do (if-let [a (rv w (g e rw/E-ACT))]
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
  (let [r (rw/new-row (g w rw/W-EPOCH) (g w rw/ID) rw/R-SIZE)]
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
    (s! r rw/R-PATH (g x (if (comp? x) rw/C-PATH rw/K-PATH)))   ; §8.2 P3: fixed at creation
    (when (comp? x) (s! r rw/R-BIND (g x rw/C-BIND)))           ; a task's: start-task!
    (if (comp? x)
      (do (s! x rw/C-RUN r)
          (s! x rw/C-RUNS (inc (gl x rw/C-RUNS))))   ; §3.2: until its retirement
      (s! x rw/K-RUN r))
    (s! w rw/W-RUNS (inc (gl w rw/W-RUNS)))     ; C1 W1: until its retirement
    (when (and (task? x) (g x rw/K-LOCAL))      ; Z#77: retired in every fork of `w`
      (s! w rw/W-LOCAL (assoc (g w rw/W-LOCAL) (g r rw/ID) r)))
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
        (when (task? x)                     ; C1c: the task completes with this scope
          (s! s rw/S-TASK x)
          (s! x rw/K-SROW s)
          (when (g x rw/K-LOCAL) (s! s rw/S-LOCAL true)))   ; Z#77
        s)))

(defn- deliver-subs!
  "Runs each live subscription [live cb] of `subs` once, after the gate."
  [w subs]
  (doseq [[live cb] subs]
    (when (hs/flag? live) (aadd! (g w rw/W-AFTER) #(when (hs/flag-cas! live true false) (cb))))))

(defn- task-complete!
  "C1c L1: task `k` is complete once done, its run retired, and its run
   scope removed or never materialized. Set once; its host joins fire."
  [w k]
  (when (and (g k rw/K-DONE) (not (g k rw/K-COMPLETE)) (nil? (rv w (g k rw/K-RUN)))
             (let [s (rv w (g k rw/K-SROW))] (or (nil? s) (g s rw/S-COMPLETE))))
    (s! k rw/K-COMPLETE true)
    (when-let [m (g w rw/W-JOIN-SUBS)]
      (let [id (g k rw/ID)]
        (when-let [subs (get m id)]
          (s! w rw/W-JOIN-SUBS (dissoc m id))
          (deliver-subs! w subs))))))

(defn- current-scope!
  "The innermost open explicit scope of the run, else its run scope."
  [w r]
  (let [ss (g r rw/R-SCOPES)]
    (if (and ss (pos? (acount ss)))
      (rv w (anth ss (dec (acount ss))))
      (run-scope! w r))))

(defn- remove-scope-if-empty!
  "T16/Z#18: a closed scope row goes once its subtree has no rows left. A run
   scope stays while its run is in cleanup (T13 step 4, Z#52), and while a
   counted fork it owns runs (C1c stage B: W-OWNED-N, or W-NORMALIZE in a
   fork until its first turn)."
  [w s]
  (when (and (not (g s rw/S-OPEN))
             (not (g s rw/S-HELD))
             (not (g s rw/S-COMPLETE))          ; removed already (a double visit)
             (not= :root (g s rw/S-KIND))       ; the administrative allowance (I11a)
             (zero? (hs/oset-count (g s rw/S-TASKS)))
             (zero? (acount (g s rw/S-CHILDREN)))
             (not (contains? (g w rw/W-OWNED-N) (id-of s)))
             (not (contains? (g w rw/W-NORMALIZE) (id-of s))))
    (unregister! w s)
    (s! s rw/S-COMPLETE true)                 ; C1c L1
    (when-let [k (rv w (g s rw/S-TASK))] (task-complete! w k))
    (when-let [p (rv w (g s rw/S-PARENT))]
      (let [cs (gm p rw/S-CHILDREN)
            i (idx-of cs s)]
        (when-not (neg? i) (hs/remove-at! cs i))
        (remove-scope-if-empty! w p)))))

(declare close-source!)

(declare release-world*)

;; Fork ownership (F2; lifecycle design v2 E1-E3, Z#58). A holder is
;; [strong-child weak-child released-flag]. A fork made by the (fork) effect is
;; held strongly by the forking run's scope: its lifetime is bounded by that
;; scope, whose close releases it and runs its finalizers. A host fork and an
;; activated instance are held weakly by the root scope: while anything can
;; still act in them (the host, a timer, an offload thread, a drainer) they
;; are reachable and the root's close releases them; once nothing can, they
;; are collected (nothing in them can run again).
(defn- holder-child [^objects h] (or (aget h 0) (hs/deref-weak (aget h 1))))
(defn- holder-dead? [^objects h] (or (hs/flag? (aget h 2)) (nil? (holder-child h))))

(defn- release-child!
  "Releases `child` (T21 in it) through its ingress; scheduled after this
   world's gate is released (E3)."
  [w child]
  (hs/mpsc-add! (g child rw/W-INGRESS) #(release-world* child))
  (aadd! (g w rw/W-AFTER) child))

(declare accept-child! kid-collected! kid-collector hold-child!)

(defn- own-child!
  "F2: the fork marker of `child` in `w`, owned by `scope`, held strongly or
   weakly (see above). An owner that has closed releases the child at once.
   C1c stage B: a strong child (the fork effect's) of an open owner is
   counted on its scope until the owner runs [:owned-done s child]."
  [w scope child strong?]
  (let [early? (or (g w rw/W-RELEASED) (not (g scope rw/S-OPEN)))
        sid (when (and strong? (not early?)) (id-of scope))]
    (when sid
      (let [m (g w rw/W-OWNED-N)]
        (s! w rw/W-OWNED-N (assoc m sid [scope (inc (long (second (get m sid [nil 0]))))]))))
    (accept-child! w child sid))      ; C1 R2: an obligation until it completes
  (hold-child! w scope child strong?))

(defn- hold-child!
  "F2: `scope` of `w` holds `child` (strongly or weakly) until it closes,
   which releases the child; a closed owner releases it at once."
  [w scope child strong?]
  (if (or (g w rw/W-RELEASED) (not (g scope rw/S-OPEN)))
    (do (release-child! w child) child)
    (let [sid (id-of scope)
          h (doto (object-array 3)
              (aset 0 (when strong? child)) (aset 1 (hs/weak child)) (aset 2 (hs/flag false)))
          m (or (g w rw/W-OWNED) (let [m (hs/vmap)] (s! w rw/W-OWNED m) m))
          ^objects e (or (hs/mget m sid) (let [e (object-array [(alist) 16])]
                                           (hs/mput! m sid e) e))
          l (aget e 0)]
    ;; dead holders (released, or collected) are pruned when the list doubles
      (when (>= (acount l) (long (aget e 1)))
        (loop [i (dec (acount l))]
          (when-not (neg? i)
            (when (holder-dead? (anth l i)) (hs/remove-at! l i))
            (recur (dec i))))
        (aset e 1 #?(:clj (num (max 16 (* 2 (acount l)))) :cljs (max 16 (* 2 (acount l))))))
      (aadd! l h)
      (s! child rw/W-HOLDER h)
      child)))

(defn- release-owned!
  "F2: the owner scope `sid` closed: each live child is released (T21) through
   its own ingress. The child is scheduled only after this world's gate is
   released (W-AFTER), so no thread takes two gates (E3)."
  [w sid]
  (when-let [m (g w rw/W-OWNED)]
    (when-let [^objects e (hs/mget m sid)]
      (hs/mdel! m sid)
      (let [l (aget e 0)]
        (dotimes [i (acount l)]
          (let [^objects h (anth l i)
                c (holder-child h)]
            (aset h 0 nil)
            (when (and c (hs/flag-cas! (aget h 2) false true))
              (release-child! w c))))))))

(defn- close-scope!
  "T16: cancels the work owned by the subtree, closes its scopes and the
   sources they own, and releases the forks it owns (F2)."
  [w s]
  (when (g s rw/S-OPEN)
    (s! s rw/S-OPEN false)
    (when-let [xs (g s rw/S-SOURCES)]
      (s! s rw/S-SOURCES nil)
      (dotimes [i (acount xs)]
        ;; resolve after the weak deref: the reference may name a basis row
        (when-let [x (rv w (hs/deref-weak (anth xs i)))] (close-source! w x))))
    (let [ts (hs/oset-vals (g s rw/S-TASKS))]
      (doseq [t ts]
        (when-let [r (rv w (g (rv w t) rw/K-RUN))] (cancel! w r ::cancelled))))
    (let [cs (acopy (g s rw/S-CHILDREN))]
      (dotimes [i (acount cs)] (close-scope! w (rv w (anth cs i)))))
    (release-owned! w (id-of s)))
  (remove-scope-if-empty! w s))

(declare release-ownership!)

(declare maybe-complete!)

(defn- retire!
  "T13, in Z#18 order."
  [w r]
  (let [x (rv w (g r rw/R-OF))]
    (if (comp? x)
      (do (when (identical? r (rv w (g x rw/C-RUN))) (s! x rw/C-RUN nil))
          (s! x rw/C-RUNS (dec (gl x rw/C-RUNS))))
      (when (identical? r (rv w (g x rw/K-RUN))) (s! x rw/K-RUN nil)))
    (s! r rw/R-MODE 2)                       ; retired
    (when-let [s (rv w (g r rw/R-SROW))]
      (s! s rw/S-HELD false)
      (close-scope! w s))
    (unregister! w r)
    (s! w rw/W-RUNS (dec (gl w rw/W-RUNS)))     ; C1 W1
    (when (and (task? x) (g x rw/K-LOCAL))      ; Z#77
      (s! w rw/W-LOCAL (not-empty (dissoc (g w rw/W-LOCAL) (g r rw/ID)))))
    (when (task? x) (task-complete! w x))       ; C1c L1: if its run scope is gone
    ;; the spent task and its owner chain go with the run (Z#56)
    (when (and (task? x) (g x rw/K-DONE)) (release-ownership! w x))
    ;; a task kept only as this run's tombstone goes now
    (when (and (task? x) (zero? (gl x rw/REFS)) (zero? (gl x rw/HANDLES))) (aadd! (g w rw/W-RQ) x))
    ;; a computation kept only as this run's tombstone (§3.2) goes now
    (when (and (comp? x) (zero? (gl x rw/REFS)) (zero? (gl x rw/HANDLES))) (aadd! (g w rw/W-RQ) x))
    ;; last: a complete world implies every task in it is complete (C1c)
    (maybe-complete! w)))

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
    (release-members! w a)
    a))

(declare link-cancelled! cancel!)

(defn- cancel-subtree!
  "C1 R4: a cancellation request reaches the whole subtree of scope `s` at
   once: the runs of its tasks and of the tasks of its explicit child scopes
   are cancelled, and the worlds these scopes own are released (their
   completion obligations stay until the children complete). Sources still
   close, and scopes are still removed, at retirement (Z#18)."
  [w s reason]
  (doseq [t (hs/oset-vals (g s rw/S-TASKS))]
    (when-let [cr (rv w (g (rv w t) rw/K-RUN))] (cancel! w cr reason)))
  (release-owned! w (id-of s))
  (let [cs (acopy (g s rw/S-CHILDREN))]
    (dotimes [i (acount cs)]
      (let [c (rv w (anth cs i))]
        (when (= :explicit (g c rw/S-KIND)) (cancel-subtree! w c reason))))))

(defn- cancel!
  "T14 `cancel(R)`. Also `cancel(R, replace)` (Y#2): only T11 and demotion
   issue a replace, always on a computation run, which has no debtor side, so
   it is the same operation; on a task run a replace is an ordinary cancel."
  [w r reason]
  ;; C1: a run that completed but still holds an unfinished await-op (its
  ;; result delivered, its start still running) gets that op cancelled
  (when (and (== rw/ACT-DONE (gl r rw/R-ACT)) (g r rw/R-RES))
    (doseq [z (vec (g r rw/R-RES))] (cancel-resource! w (rv w z))))
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
      (doseq [z (vec zs)] (cancel-resource! w (rv w z))))   ; M5: this world's copy, never the basis
    ;; children: the whole run-scope subtree, now (C1 R4)
    (when-let [s (rv w (g r rw/R-SROW))] (cancel-subtree! w s reason))
    (let [x (rv w (g r rw/R-OF))]
      (when (task? x)
        ;; debtor side (R#14): the task fails with ::cancelled
        (finish-task! w x (cancelled-ex reason) true)
        (when-let [l (g x rw/K-LINK)] (link-cancelled! (rv w l)))))
    (retire-check! w r)))

(defn- slice!
  "Runs `f` as a slice of `r` on the host stack, restoring the caller's
   active run afterwards (I10)."
  [r f]
  (let [prev (active-run)
        c (ctx)
        #?@(:clj [pf (thread-frame)
                  rf (or (g r rw/R-BIND) pf)]
            :cljs [po (aget c 3)])]
    (s! r rw/R-SLICE true)
    (set-active! r)
    (aset c 2 #?(:clj (num (inc (long (aget c 2)))) :cljs (inc (aget c 2))))
    #?(:clj (when-not (identical? pf rf) (clojure.lang.Var/resetThreadBindingFrame rf))
       :cljs (let [m (g r rw/R-BIND)]
               (aset c 3 nil)
               (when m (let [t (volatile! {})] (aset c 3 t) (install-bindings! m t)))))
    (try
      (try (force! (f))
           (catch #?(:clj Throwable :cljs :default) t
             (complete! (or (active-run) r) t true)))
      (finally
        ;; re-resolve: a fork effect in this slice made `r` a shared basis row
        (aset c 2 #?(:clj (num (dec (long (aget c 2)))) :cljs (dec (aget c 2))))
        #?(:clj (let [f (thread-frame)]
                  (s! (rv (cw) r) rw/R-BIND f)
                  (when-not (identical? f pf) (clojure.lang.Var/resetThreadBindingFrame pf)))
           :cljs (let [t (aget c 3)]
                   (when t
                     (let [r (rv (cw) r)]
                       (when-let [m (g r rw/R-BIND)] (s! r rw/R-BIND (read-back m))))
                     (reduce-kv (fn [_ _ [st outer]] (st outer)) nil @t))
                   (aset c 3 po)))
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

(defn- release-adopted! [w x]
  ;; §5.2: a task the new run did not re-spawn is cancelled
  (when (and (task? x) (rv w (g x rw/K-RUN))) (cancel! w (rv w (g x rw/K-RUN)) ::cancelled))
  (ref-dec! w x))

(defn- take-rejected!
  "Z#83: the keyed rows rejected from the kept prefix (C-REJ) leave the
   basis, in one pass; returns them. They belong to the adoption basis."
  [w c]
  (when-let [rej (g c rw/C-REJ)]
    (s! c rw/C-REJ nil)
    (let [ids (into #{} (map #(g % rw/ID)) rej)
          basis (gm c rw/C-BASIS)
          n (acount basis)]
      (loop [i 0 j 0]
        (if (< i n)
          (let [x (rv w (anth basis i))]
            (if (contains? ids (g x rw/ID))
              (recur (inc i) j)
              (do (aput! basis j x) (recur (inc i) (inc j)))))
          (dotimes [_ (- n j)] (apop! basis))))
      rej)))

(defn- release-adoption! [w c]
  (s! c rw/C-KEPT-K nil)   ; no additional retention references: its rows are the basis's
  (doseq [x (take-rejected! w c)] (release-adopted! w (rv w x)))
  (when-let [ab (g c rw/C-ADOPT)]
    (s! c rw/C-ADOPT nil)
    (dotimes [i (acount ab)] (release-adopted! w (rv w (anth ab i)))))
  (when-let [abk (g c rw/C-ADOPT-K)]
    (s! c rw/C-ADOPT-K nil)
    (doseq [x (vals abk)] (release-adopted! w (rv w x))))
  (when-let [bs (g c rw/C-ADOPT-BASE)]
    (s! c rw/C-ADOPT-BASE nil)
    (dotimes [i (acount bs)] (ref-dec! w (rv w (g (rv w (anth bs i)) rw/E-DEBTOR))))))

(defn- drop-adoption!
  "Ends the references of an adoption basis `ab` (and its keyed part `abk`)
   and baselines `bs` the computation no longer holds."
  [w ab abk bs]
  (when ab (dotimes [i (acount ab)] (ref-dec! w (rv w (anth ab i)))))
  (doseq [x (vals abk)] (ref-dec! w (rv w x)))
  (when bs (dotimes [i (acount bs)] (ref-dec! w (rv w (g (rv w (anth bs i)) rw/E-DEBTOR))))))

(defn- release-ownership!
  "A done task leaves its owner scope once its run has retired: until then the
   cleanup entry keeps it as a tombstone, and its owner chain (§3.2, Z#56)."
  [w k]
  (let [owner (rv w (g k rw/OWNER))]
    (when (and owner (not (fn? owner)) (== rw/T-SCOPE (gl owner rw/TYPE)))
      (when (hs/oset-del! (gm owner rw/S-TASKS) (id-of k))
        (ref-dec! w k))
      (remove-scope-if-empty! w owner))))

(declare link-done! link-cancelled!)

(defn- finish-task!
  "Sets a task's result and fires its creditors; ownership retention ends
   with its run (release-ownership!)."
  [w k v err?]
  (when-not (g k rw/K-DONE)
    (s! k rw/K-DONE true)
    (s! k rw/K-RESULT v)
    (s! k rw/K-ERR (boolean err?))
    (s! k rw/VERSION (inc (gl k rw/VERSION)))
    (settle! w k)
    (when-not (rv w (g k rw/K-RUN))
      (task-complete! w k)
      (release-ownership! w k))))

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
          ;; Q10: children not awaited and not detached are cancelled, in the
          ;; whole run-scope subtree (C1 R4)
          (when-let [s (rv w (g r rw/R-SROW))] (cancel-subtree! w s ::cancelled))
          (finish-task! w x v err?)
          (s! r rw/R-SLICE false)
          (retire-check! w r)
          (commit! w [:complete (g r rw/ID) (if err? 2 1) [:opaque v]])
          ;; a realizer's completion realizes its link in the next item (C0)
          (when-let [l (g x rw/K-LINK)] (link-done! w (rv w l) v err?))))))
  nil)

;; ---------------------------------------------------------------------------
;; Dispatch (T5, T11)

(defn- earliest-fired [w c]
  (let [ins (g c rw/C-INS)]
    (loop [i 0]
      (when (< i (acount ins))
        (let [e (rv w (anth ins i))]
          (if (g e rw/E-ARMED) (recur (inc i)) i))))))

(defn- restore-ordinals!
  "T11 resume: the creation counts continue from the creations kept in the
   basis (§5.2): positional ordinals per site, keyed counts per [site K]."
  [w c r]
  (when-let [basis (g c rw/C-BASIS)]
    (when (pos? (acount basis))
      (let [ords (hs/vmap)]
        (dotimes [i (acount basis)]
          (let [key (g (rv w (anth basis i)) rw/KEY)]
            (if (vector? key)
              (let [sk (subvec key 0 2)
                    nxt (inc (long (nth key 2)))
                    kord (or (g r rw/R-KORD) {})]
                (when (> nxt (long (get kord sk 0))) (s! r rw/R-KORD (assoc kord sk nxt))))
              (let [key (long key)
                    ord (mod key 1048576)                 ; floors, as the encode: site -1 is negative
                    site (quot (- key ord) 1048576)       ; exact: key - ord is a multiple of 2^20
                    nxt (inc ord)
                    cur (long (or (hs/mget ords site) 0))]
                (when (> nxt cur) (hs/mput! ords site nxt))))))
        (s! r rw/R-ORD ords)))))

;; ---------------------------------------------------------------------------
;; Delta log (§4.4): a signal or cell keeps the deltas of its last writes,
;; truncated at a constant bound. X-DLOG is nil (nothing known before the
;; current version) or [from ds], `ds` holding one entry per version in
;; (from, version]. A write with unknown deltas (a plain write) resets it.

(def ^:const delta-bound 32)

(defn- log-deltas! [x ver ds]
  (if (nil? ds)
    (s! x rw/X-DLOG nil)
    (let [[from l] (or (g x rw/X-DLOG) [(dec (long ver)) []])
          l (conj l ds)]
      (s! x rw/X-DLOG (if (> (count l) delta-bound)
                        [(inc (long from)) (into [] (subvec l 1))]
                        [from l])))))

(defn- deltas-since
  "The composed deltas of `x` since version `since`, or nil when they are
   not available (a plain write or truncation in between)."
  [x since]
  (when-let [[from l] (g x rw/X-DLOG)]
    (let [since (long since) from (long from)]
      (when (>= since from)
        (reduce into [] (subvec l (- since from)))))))

(defn- resume-k
  "Resumes a parked body at `k` with `v`. A throw from the resumed code
   before its next suspension belongs to the handler that was in scope at
   the suspension (`ek`), as it would without the suspension: the lexical
   `try` around the effect has returned by now."
  [k ek v]
  (try (k v) (catch #?(:clj Throwable :cljs :default) t (ek t))))

(defn- has-base?
  "The model's `has-base` of a dep edge (§4.4): it consumed a version (a
   track, a delivered await re-armed with its result, a reactivation edge),
   or its debtor is a signal or cell (an await's baseline). A pending await
   of a computation, task, deferred or link has none."
  [w e]
  (or (some? (g e rw/E-SEEN))
      (let [d (rv w (g e rw/E-DEBTOR))]
        (and (source? d) (<= (gl d rw/X-KIND) rw/SRC-CELL)))))

(defn- dispatch!
  "T11 (and T5 for a computation without a fired edge): starts the
   computation's next run, re-entering at its earliest fired dep edge when
   that site is re-entrant (X#2)."
  [w c]
  (s! c rw/C-QUEUED false)
  (when (needs-run? w c)
    (when-let [old (rv w (g c rw/C-RUN))] (cancel! w old ::cancelled))
    (let [ins (gm c rw/C-INS)
          restart? (g c rw/C-RESTART)
          ei (when-not restart? (earliest-fired w c))
          e (when ei (rv w (anth ins ei)))
          at (if e (gl e rw/E-AT) -1)]
      (s! c rw/C-RESTART false)
      ;; The cut (`comp-cut-row`): the latest suffix replaces the adoption
      ;; basis and baselines, also when it is empty. The previous ones are
      ;; dropped once the suffix holds its references; Rule R cancels a
      ;; task nothing else retains (§3.3 step 1.2).
      (let [old-ab (g c rw/C-ADOPT)
            old-abk (g c rw/C-ADOPT-K)
            old-bs (g c rw/C-ADOPT-BASE)]
        (s! c rw/C-ADOPT nil)
        (s! c rw/C-ADOPT-K nil)
        (s! c rw/C-ADOPT-BASE nil)
        (s! c rw/C-KEPT-K nil)
        ;; Suffix: dep edges after E are removed; those with a baseline keep
        ;; their debtors through the adoption baselines (§4.4, Z#21; the
        ;; model's `bases-of`). The baselines take their references before
        ;; any suffix edge is unlinked.
        (let [keep (if ei (inc (long ei)) (if restart? 0 (acount ins)))]
          (when (> (acount ins) keep)
            (let [bs (alist)
                  gone (alist)]
              (loop []
                (when (> (acount ins) keep)
                  (let [x (rv w (apop! ins))]
                    (when (has-base? w x)
                      (ref-inc! (rv w (g x rw/E-DEBTOR)))
                      (aadd! bs x))
                    (aadd! gone x))
                  (recur)))
              (dotimes [i (acount gone)] (unlink! w (anth gone i)))
              (s! c rw/C-ADOPT-BASE bs))))
        ;; Suffix creations become the adoption basis: keyed ones (Z#82) by
        ;; their creation key, positional ones in a list. The rows the last
        ;; run rejected from the basis (Z#83) were adoption rows: dropped.
        (let [rej (take-rejected! w c)
              basis (g c rw/C-BASIS)]
          (when (and basis (pos? (acount basis)))
            (let [ab (alist)
                  kept (alist)
                  abk (loop [i 0 abk (transient {})]
                        (if (< i (acount basis))
                          (let [x (rv w (anth basis i))]
                            (if (or restart? (> (gl x rw/AT) at))
                              (let [key (g x rw/KEY)]
                                (if (vector? key)
                                  (recur (inc i) (assoc! abk key x))
                                  (do (aadd! ab x) (recur (inc i) abk))))
                              (do (aadd! kept x) (recur (inc i) abk))))
                          (persistent! abk)))]
              (s! c rw/C-BASIS kept)
              (s! c rw/C-ADOPT ab)
              (s! c rw/C-ADOPT-K (not-empty abk))
              ;; A run that restarts from the body (E without a continuation)
              ;; counts its creations afresh, so it re-creates the kept prefix
              ;; too: its keyed rows are indexed by key (positional ones are
              ;; found in the basis).
              (when (and e (nil? (g e rw/E-CONT)))
                (s! c rw/C-KEPT-K (not-empty (loop [i 0 kk (transient {})]
                                               (if (< i (acount kept))
                                                 (let [x (anth kept i) key (g x rw/KEY)]
                                                   (recur (inc i) (if (vector? key) (assoc! kk key x) kk)))
                                                 (persistent! kk))))))))
          (drop-adoption! w old-ab old-abk old-bs)
          (doseq [x rej] (ref-dec! w (rv w x)))))
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
                   (let [ds (when (source? d) (deltas-since d (gl e rw/E-SEEN)))]
                     (s! e rw/E-SEEN (g d rw/VERSION))
                     (if (source? d)
                       (let [old (g e rw/E-BASE) v (g d rw/X-VALUE)
                             ek (g e rw/E-ERRK)]
                         (s! e rw/E-BASE v)
                         #(resume-k k ek (iv/->Interval old v ds)))
                       (let [[v err?] (debtor-result d)
                             ek (g e rw/E-ERRK)]
                         (when (final? d) (remove-dep! w e))   ; consumed: removed, not re-armed
                         (if err? #(ek v) #(resume-k k ek v))))))
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
  (when-let [bs (gm c rw/C-ADOPT-BASE)]
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
   c's creditors; reaching `d` again means the new edge closes a cycle. The
   raise is planned first and written only when it closes no cycle: a
   refused edge (::cycle) changes no rank."
  [w c d]
  (let [need (inc (gl d rw/C-RANK))]
    (if (>= (gl c rw/C-RANK) need)
      true
      (let [plan (loop [todo [[c need]] plan {}]
                   (if-let [[x n] (peek todo)]
                     (let [todo (pop todo)
                           id (g x rw/ID)
                           cur (max (gl x rw/C-RANK) (long (or (second (get plan id)) 0)))]
                       (cond
                         (identical? x d) nil
                         (>= cur (long n)) (recur todo plan)
                         :else
                         (let [outs (g x rw/OUTS)]
                           (recur (loop [i 0 todo todo]
                                    (if (< i (acount outs))
                                      (let [e (rv w (anth outs i))]
                                        (recur (inc i)
                                               (if (== rw/EK-DEP (gl e rw/E-KIND))
                                                 (conj todo [(rv w (g e rw/E-CRED)) (inc (long n))])
                                                 todo)))
                                      todo))
                                  (assoc plan id [x n])))))
                     plan))]
        (if (nil? plan)
          false
          (do (doseq [[x n] (vals plan)] (s! x rw/C-RANK n))
              true))))))

(defn cycle-ex [c d]
  (ex-info "dependency cycle" {:spindel/cycle [(g c rw/ID) (g d rw/ID)]}))

(defn- site-edge!
  "The dep edge of `c` at site `at` on `d`: reused when the prefix already
   has it, otherwise created. Returns [edge reused?]. A new edge that would
   close a computation cycle is refused (I12): returns [nil false]."
  [w r c d at k ek]
  (let [ins (gm c rw/C-INS)
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
   finalizers (no open region and no running finally clause) or resources.
   A site inside a running clause is not re-entrant: T11 would resume the
   new run inside a clause it never entered (B3, B8)."
  [r k]
  (when (and (zero? (fins r)) (zero? (long (or (g r rw/R-INFIN) 0))) (nil? (g r rw/R-RES))) k))

(defn enter-finally!
  "Body contract: a `finally` region opens (rewritten by the body macros)."
  []
  (when-let [r (active-run)]
    (s! r rw/R-FINS (inc (fins r)))
    (commit! (cw) [:finally-enter (g r rw/ID)])))

(defn exit-finally!
  "A `finally` region closes; its block runs now (C1 W4: the run is in a
   finally clause until `leave-finalizer!`)."
  []
  (when-let [r (active-run)]
    (s! r rw/R-FINS (max 0 (dec (fins r))))
    (s! r rw/R-INFIN (inc (long (or (g r rw/R-INFIN) 0))))
    (commit! (cw) [:finally-exit (g r rw/ID)])))

(defn leave-finalizer!
  "The finally clause entered by `exit-finally!` ended (also by a throw).
   Without a running clause it is refused, as in the model (a refused log
   entry), and throws: the body broke the region protocol."
  []
  (when-let [r (active-run)]
    (let [n (long (or (g r rw/R-INFIN) 0))]
      (if (zero? n)
        (do (refuse! (cw) [:finally-leave (g r rw/ID)])
            (throw (ex-info "finally-leave without a running finally clause (B3)"
                            {:spindel/invalid :finally-leave})))
        (do (s! r rw/R-INFIN (dec n))
            (commit! (cw) [:finally-leave (g r rw/ID)]))))))

(defn- finalizer-refusal
  "C1 W4 (B8 reduced to suspension): finalizers are synchronous. A
   suspending effect inside a finally clause, on normal and cancellation
   entry alike, fails with this error; nil when allowed."
  []
  (when-let [r (active-run)]
    (when (pos? (long (or (g r rw/R-INFIN) 0)))
      (ex-info "a finally clause may not suspend (finalizers are synchronous)"
               {:spindel/invalid :finalizer}))))

(defn- unwinding-finalizer-refusal
  "In a finally clause of a cancelled run, every effect is refused
   explicitly (even one that would not suspend): the run cannot take
   effects any more, and silently dropping the continuation would skip the
   rest of the cleanup."
  []
  (when-let [r (active-run)]
    (when (and (pos? (long (or (g r rw/R-INFIN) 0))) (== rw/ACT-DONE (gl r rw/R-ACT)))
      (finalizer-refusal))))

(defn- invalid-op [op msg] (ex-info msg {:spindel/invalid op}))

(defn- kind-ok?
  "The kinds a host source operation applies to (the model's writable,
   deliverable, open-kind, takeable and t20-pin guards)."
  [x op]
  (case op
    :write (and (source? x) (<= (gl x rw/X-KIND) rw/SRC-CELL))
    :deliver (and (source? x) (== rw/SRC-DEFERRED (gl x rw/X-KIND)))
    :post (and (source? x) (== rw/SRC-MAILBOX (gl x rw/X-KIND)))
    :release (and (source? x) (== rw/SRC-SEMAPHORE (gl x rw/X-KIND)))
    :take (and (source? x) (<= rw/SRC-MAILBOX (gl x rw/X-KIND) rw/SRC-SEMAPHORE))
    ;; tasks too (a pin keeps a task's row and result, e.g. tooling); the
    ;; model's t20-pin takes computations and sources only (to be widened)
    :pin (or (comp? x) (source? x) (task? x))))

(def ^:private kind-msg
  {:write "write! is for signals and cells" :deliver "deliver! is for deferreds"
   :post "post! is for mailboxes" :release "release is for semaphores"
   :take "take!/acquire! are for mailboxes and semaphores" :pin "pin! is for computations, tasks and sources"})

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
                b (when-not reused? (adoption-baseline! w c at x))
                old (if reused? (g e rw/E-BASE) (when b (g b rw/E-BASE)))
                ds (cond reused? (deltas-since x (gl e rw/E-SEEN))
                         b (deltas-since x (gl b rw/E-SEEN)))]
            (s! e rw/E-BASE v)
            (s! e rw/E-SEEN (g x rw/VERSION))
            (s! e rw/E-ARMED true)
          ;; Z#48: a closed (final) source delivers once; its edge is consumed
            (when (final? x) (remove-dep! w e))
            (commit! w [:track (g r rw/ID) (g x rw/ID) [:opaque k] (if reused? 0 (g e rw/ID))])
            (k (iv/->Interval old v ds)))))
      (unwind! ek))))

(defn- new-activation! [w aid r mode k ek ^objects members ^objects slots remaining]
  (let [a (rw/new-row (g w rw/W-EPOCH) (g w rw/ID) rw/A-SIZE)]
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
   values (or, fail-fast, its first error: Z#61), `any` the winning slot."
  [mode ^objects slots winner]
  (case mode
    :one (aget slots 0)
    :any (aget slots (int winner))
    :all (if (some? winner)
           (aget slots (int winner))
           (let [n (alength slots)]
             (loop [i 0 acc (transient [])]
               (if (< i n)
                 (let [[v err?] (aget slots i)]
                   (if err? [v true] (recur (inc i) (conj! acc v))))
                 [(persistent! acc) false]))))))

(defn- continue! [res k ek]
  (let [[v err?] res] (if err? (ek v) (resume-k k ek v))))

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
    (when (and (or (= :any (g a rw/A-MODE)) (and (= :all (g a rw/A-MODE)) (some? (g a rw/A-WINNER))))
               (not (comp? (rv w (g r rw/R-OF)))))
      (cancel-losers! w r (g a rw/A-MEMBERS)))
    (release-members! w a)
    (s! a rw/A-RESULT (group-result (g a rw/A-MODE) (g a rw/A-SLOTS) (g a rw/A-WINNER)))
    (s! a rw/A-RESUMED true)
    (when-not (g a rw/A-INLINE)
      (aadd! (g w rw/W-RESUME) a))))

(declare notify-blocked-walk!)

(defn- notify-blocked!
  "§4.5.6-7: `x` parked. Creditors with a marked edge from it may now be
   eligible, and entities parked on it may now be blocked in turn."
  [x depth]
  (if (>= (long depth) 64)
    (notify-blocked-walk! x)
    (let [w (cw)
          outs (g x rw/OUTS)]
      (dotimes [i (acount outs)]
        ;; an edge's kind never changes after link!: read it from the reference,
        ;; so an observe edge a fork inherited is neither viewed nor copied
        (let [e0 (anth outs i)
              k (gl e0 rw/E-KIND)]
          (cond
            (== k rw/EK-DEP)
            (let [e (peek-row w e0)
                  c (rv w (g e rw/E-CRED))]
              (when (g e rw/E-MARKED) (maybe-schedule! w c))
              (when (g e rw/E-ACT) (notify-blocked! c (inc (long depth)))))
            (== k rw/EK-WAIT)
            (let [e (peek-row w e0)
                  a (rv w (g e rw/E-CRED))]
              (when (and (some? a) (not (fn? a)) (act? a))
                (notify-blocked! (rv w (g (rv w (g a rw/A-RUN)) rw/R-OF)) (inc (long depth)))))))))))

(defn- notify-blocked-walk!
  "notify-blocked! from depth 64 on: the same propagation as a worklist,
   each entity once (a cycle of waits ends it)."
  [x0]
  (let [w (cw)]
    (loop [todo [x0] seen #{}]
      (when-let [x (peek todo)]
        (let [todo (pop todo)
              id (g x rw/ID)]
          (if (contains? seen id)
            (recur todo seen)
            (let [outs (g x rw/OUTS)
                  todo (loop [i 0 todo todo]
                         (if (< i (acount outs))
                           (let [e0 (anth outs i)
                                 k (gl e0 rw/E-KIND)]
                             (recur (inc i)
                                    (cond
                                      (== k rw/EK-DEP)
                                      (let [e (peek-row w e0)
                                            c (rv w (g e rw/E-CRED))]
                                        (when (g e rw/E-MARKED) (maybe-schedule! w c))
                                        (if (g e rw/E-ACT) (conj todo c) todo))
                                      (== k rw/EK-WAIT)
                                      (let [e (peek-row w e0)
                                            a (rv w (g e rw/E-CRED))]
                                        (if (and (some? a) (not (fn? a)) (act? a))
                                          (conj todo (rv w (g (rv w (g a rw/A-RUN)) rw/R-OF)))
                                          todo))
                                      :else todo)))
                           todo))]
              (recur todo (conj seen id)))))))))

(defn- mine-of
  "The `any` loser candidates of an await (T6): member tasks the run created
   (owned by its run scope)."
  [w r ds]
  (let [s (rv w (g r rw/R-SROW))]
    (vec (for [d ds :let [d (row-of d)]
               :when (and (task? d) s (identical? s (rv w (g d rw/OWNER))))]
           (g d rw/ID)))))

(defn- comp-debtors
  "The computation debtors `y` depends on: its live dep edges, or for an
   idle `y` the debtors its validity records (the edges a reactivation
   would re-link)."
  [w y]
  (if (g y rw/C-IDLE)
    (let [vs (g y rw/C-VALIDITY)]
      ;; a fresh one is never reactivated: its validity re-links nothing
      (if (and (sequential? vs) (some? (g y rw/C-DONE-EPOCH)))
        (into [] (keep (fn [[d]] (let [d (rv w d)] (when (and d (comp? d)) d)))) vs)
        []))
    (let [ins (g y rw/C-INS)]
      (loop [i 0 acc []]
        (if (and ins (< i (acount ins)))
          (let [e (rv w (anth ins i))
                d (when e (rv w (g e rw/E-DEBTOR)))]
            (recur (inc i) (if (and d (comp? d)) (conj acc d) acc)))
          acc)))))

(defn- await-cycle
  "T6's cycle check on the unchanged world (the model's await-cycle, before
   any reactivation, edge or raise): the first computation member from
   which `x` is reachable through computation debtors, or nil."
  [w x ds]
  (let [xid (long (g x rw/ID))]
    (some (fn [h]
            (let [d (row-of h)]
              (when (comp? d)
                (loop [todo [d] seen #{}]
                  (when-let [y (peek todo)]
                    (let [todo (pop todo) id (long (g y rw/ID))]
                      (cond (== id xid) d
                            (contains? seen id) (recur todo seen)
                            :else (recur (into todo (comp-debtors w y)) (conj seen id)))))))))
          ds)))

(defn- await-group!
  "T6: an activation over `ds` with `mode` (:one :all :any). A cycle is
   refused before anything changes (the model's refusal is atomic)."
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
        (when in-comp?
          (when-let [d (await-cycle w x ds)] (vreset! refused d)))
      ;; Reactivation of valid idle debtors first, then member edges in
      ;; debtor-list order (the model's allocation order).
        (when-not @refused
          (dotimes [i n]
            (let [d (row-of (nth ds i))]
              (when (and (comp? d) (g d rw/C-IDLE)) (validate! w d)))))
      ;; Member edges; a repeated debtor shares its edge.
        (dotimes [i (if @refused 0 n)]
          (let [d (row-of (nth ds i))
                prev (loop [j 0] (when (< j i)
                                   (let [m (rv w (aget members j))]
                                     (if (and m (identical? d (rv w (g m rw/E-DEBTOR)))) m (recur (inc j))))))]
            (cond
              prev (aset members i prev)
              in-comp? (let [[e reused?] (site-edge! w r x d at kk ek)]
                         (if (nil? e)
                           (vreset! refused d)
                           (do (when (and (source? d) (not (deferred? d))) (s! e rw/E-BASE (g d rw/X-VALUE)))
                               ;; §4.4: a suffix debtor stays cached until the new run awaits
                               ;; it again: the re-await's own edge retains it now
                               (when-not reused? (adoption-baseline! w x at d))
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
                  (when (or (= mode :any) (and (= mode :all) (nth (aget slots i) 1)))
                    (vreset! winner i)))))
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
                                    ;; a copy: remove-dep! shrinks C.ins
                                    (let [ins (acopy (g x rw/C-INS))]
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

(defn- settled-now?
  "Whether an await on `d` completes without suspending (C1 W4): a value
   read at once, or a settled debtor."
  [d]
  (or (and (source? d) (not (deferred? d)) (not (consuming? d)) (not (stream? d)))
      (and (not (and (comp? d) (g d rw/C-IDLE))) (settled? d))))

(defn- stream-ex [] (invalid-op :await "a stream is read through its positions: (position s)"))

(defn await-effect!
  "T6 with mode `one`; on a mailbox it is `take` (Z#54)."
  [d k ek]
  (if-let [refusal (or (unwinding-finalizer-refusal) (when-not (settled-now? (row-of d)) (finalizer-refusal)))] (ek refusal)
          (cond
            (stream? d) (ek (stream-ex))
            (consuming? d)
            (if (== rw/SRC-MAILBOX (gl d rw/X-KIND))
              (consume-effect! d k ek)
              (ek (invalid-op :await "await on a semaphore: use acquire!")))
            :else (await-group! [d] :one k ek))))

(defn- group-effect! [ds mode k ek]
  (let [ds (vec ds)]
    (if-let [refusal (or (when (and (= mode :any) (empty? ds))
                           (invalid-op :any "await-any needs at least one input"))
                         (unwinding-finalizer-refusal)
                         (when-not (if (= mode :any)
                                     (some #(settled-now? (row-of %)) ds)
                                     (every? #(settled-now? (row-of %)) ds))
                           (finalizer-refusal)))]
      (ek refusal)
      (cond
        (some #(consuming? (row-of %)) ds)
        (ek (invalid-op mode "a group await cannot take from a mailbox or semaphore"))
        (some #(stream? (row-of %)) ds) (ek (stream-ex))
        :else (await-group! ds mode k ek)))))

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
(declare host-call! write! deliver! post! handle-swap! handle-claim! handle-watch! handle-unwatch! handle-watches)

(deftype Handle [w ^objects cell dropped]
  ;; @h is the host read (B7 outside bodies). On a signal or cell, reset! and
  ;; swap! write it; invoking a deferred delivers it (true when this call won),
  ;; invoking a mailbox posts to it (M6 R8).
  #?@(:clj [clojure.lang.IDeref
            (deref [this] (value this))
            clojure.lang.IAtom
            (reset [this v] (write! this v) v)
            (swap [this f] (handle-swap! this #(f %)))
            (swap [this f a] (handle-swap! this #(f % a)))
            (swap [this f a b] (handle-swap! this #(f % a b)))
            (swap [this f a b xs] (handle-swap! this #(apply f % a b xs)))
            (compareAndSet [this o n] (handle-swap! this #(if (identical? % o) n %) (fn [old _] (identical? old o)) false))
            clojure.lang.IRef
            (addWatch [this k f] (handle-watch! this k f) this)
            (removeWatch [this k] (handle-unwatch! this k) this)
            (getWatches [this] (handle-watches this))
            (getValidator [_] nil)
            (setValidator [_ _] (throw (ex-info "signals take no validator" {:spindel/invalid :validator})))
            clojure.lang.IFn
            (invoke [this v] (handle-claim! this v))
            (applyTo [this args] (if (== 1 (count args)) (handle-claim! this (first args))
                                     (throw (clojure.lang.ArityException. (count args) "Handle"))))]
      :cljs [IReset (-reset! [this v] (write! this v) v)
             ISwap
             (-swap! [this f] (handle-swap! this #(f %)))
             (-swap! [this f a] (handle-swap! this #(f % a)))
             (-swap! [this f a b] (handle-swap! this #(f % a b)))
             (-swap! [this f a b xs] (handle-swap! this #(apply f % a b xs)))
             IFn (-invoke [this v] (handle-claim! this v))
             IWatchable
             (-add-watch [this k f] (handle-watch! this k f) this)
             (-remove-watch [this k] (handle-unwatch! this k) this)
             (-notify-watches [_ _ _] nil)]))

(declare host! handle-drop! href)

(defn- watchable-source? [row]
  (and row (== rw/T-SOURCE (gl row rw/TYPE)) (<= (gl row rw/X-KIND) rw/SRC-CELL)))

(defn- source-token-drop!
  "The canonical source token's T19 bookkeeping, without an engine turn.
   A source with no refs/handles can only leave the verify registry: there
   are no graph edges, slices or callbacks to retire. It hands off after
   releasing the gate (H2)."
  [w row]
  (let [lk (g w rw/W-LOCK)]
    (cond
      (not (hs/try-lock! lk))
      (hs/metadata-later! #(source-token-drop! w row) 1)
      ;; Z#77: a fork's first item is its retirement (T28): an empty
      ;; internal item enters it through the ordinary path, then this retries
      (g w rw/W-RETIRE)
      (do (hs/unlock! lk)
          (internal! w (fn [] nil))
          (hs/metadata-later! #(source-token-drop! w row) 1))
      :else
      (do
        (try
          (when-not (g w rw/W-META-CLOSED)
            (lt/locked
             (fn []
               (let [x (rv w row)]
                 (when (and (pos? (gl x rw/HANDLES))
                            (not (lt/live-token? (g w rw/W-WATCHES) (g x rw/ID))))
                   (s! x rw/HANDLES (dec (gl x rw/HANDLES)))
                   (when (and (zero? (gl x rw/HANDLES)) (zero? (gl x rw/REFS)))
                     (unregister! w x))
              ;; Keep the verify ledger, but never call its embedder hook
              ;; (or commit!/Rule R, which can execute unrelated graph work).
                   (when-let [log (g w rw/W-LOG)]
                     (aadd! log {:item [:handle-drop (g x rw/ID)] :accepted true})))))))
          (finally (hs/unlock! lk)))
        (handoff! w)))))

(defn- attach-watch-token! [w cell row]
  (when (watchable-source? row)
    (let [on-death (when (some? (g w rw/W-REG))
                     (let [ww (hs/weak w) wr (hs/weak row)]
                       (fn []
                         (when-let [w (hs/deref-weak ww)]
                           (when-let [row (hs/deref-weak wr)]
                             (hs/metadata-later! #(source-token-drop! w row)))))))]
      ;; Source aliases share one existing logical handle allowance. Its GC
      ;; drop follows the canonical token, not whichever alias dies first.
      (lt/source-token! (g w rw/W-WATCHES) (g row rw/ID) cell on-death))))

(defn- new-handle
  "A fresh handle object for `w`; T19 is enqueued when it is collected. The
   cleaning action holds the cell and the flag, never the handle."
  [w row]
  (let [cell (object-array 3)
        dropped (hs/flag false)
        h (Handle. w cell dropped)]
    (aset cell 0 row)
    (attach-watch-token! w cell row)
    ;; T19 on collection matters only where the engine keeps rows that have no
    ;; engine reason: the verify registry. In production such rows are held by
    ;; their handles alone, so the host GC frees them with the handle, and no
    ;; Cleaner traffic competes for the gate (§1, G1).
    (when (and (some? (g w rw/W-REG)) (not (watchable-source? row)))
      (let [ww (hs/weak w)
            row-cell (object-array [row])]
        ;; Do not capture cell: its source watch token may capture the handle.
        ;; Top handles bind the separate cleaning cell when their row commits.
        (aset cell 2 {:drop-row row-cell})
        (hs/on-collect! h (fn []
                            (when-let [row (aget row-cell 0)]
                              (when (hs/flag-cas! dropped false true)
                                (when-let [w (hs/deref-weak ww)]
                                  (host! w #(handle-drop! w row)))))))))
    h))

(defn- handle!
  "The row's live handle, or a new one (+1 handle, Z#29). A row has at most
   one live handle object. A row copied into a fork inherits its count but no
   handle object (handles are per world, §8.1): the fork's first handle takes
   over the inherited count instead of adding one."
  [w row]
  (or (let [r (g row rw/HREF)] (if (instance? Handle r) r (hs/deref-weak r)))
      (let [h (new-handle w row)
            again? (some? (g row rw/HREF))
            acquire? (if again?
                       (or (not (watchable-source? row)) (zero? (gl row rw/HANDLES)))
                       ;; no handle object yet: a new row (0), or a fork's copy (its inherited count)
                       (zero? (gl row rw/HANDLES)))]
        ;; Source aliases share one logical allowance, owned by their token.
        ;; Replacing a dead canonical HREF does not acquire a second allowance.
        (when acquire? (s! row rw/HANDLES (inc (gl row rw/HANDLES))))
        (s! row rw/HREF (href w h))
        (when (and again? acquire?) (commit! w [:handle-new (g row rw/ID)]))
        h)))

(defn- href
  "How a row holds its live handle: weakly in verify mode, where collection
   drives T19 (Cleaner), strongly otherwise, where nothing depends on it and
   the host GC frees row and handle together."
  [w h]
  (if (or (some? (g w rw/W-REG))
          (watchable-source? (aget ^objects (.-cell ^Handle h) 0)))
    (hs/weak h)
    h))

(defn- top-handle
  "A handle returned before its creating item commits (H1)."
  [w]
  (new-handle w nil))

(defn- bind-handle!
  "The creating item commits. Cold pending world-refs receive only the row,
   never the Handle's source token or foreign-world ownership metadata."
  [h row]
  (let [cell (.-cell ^Handle h)]
    (aset ^objects cell 0 row)
    (when-let [drop-row (:drop-row (aget ^objects cell 2))]
      (aset ^objects drop-row 0 (when-not (watchable-source? row) row)))
    (when (:ref-cells (aget ^objects cell 2))
      (lt/locked #(let [m (aget ^objects cell 2)]
                    (doseq [ref-cell (:ref-cells m)] (aset ^objects ref-cell 0 row))
                    (aset ^objects cell 2 (dissoc m :ref-cells)))))
    (attach-watch-token! (.-w ^Handle h) cell row))
  (s! row rw/HREF (href (.-w ^Handle h) h)))

(defn- inherited?
  "Whether row `x` is in world `w`: created by `w`, or by an ancestor before
   the fork that leads to `w` (§8.1). The walk stops at the first fork point
   older than the row, so it is as long as the row is young."
  [w x]
  (let [c (rw/creator x) id (long (g x rw/ID))]
    (or (= c (g w rw/ID))
        (loop [l (g w rw/W-LINEAGE)]
          (when-let [[a cut] (first l)]
            (when (< id (long cut))
              (or (= c a) (recur (rest l)))))))))

(defn- lineage-ex [x]
  (ex-info "the row belongs to a world outside this world's lineage"
           {:spindel/invalid :lineage :row (g x rw/ID)}))

(defn row-of
  "The row behind a handle, as the processed world sees it. A handle of
   another world must name a row this world inherited."
  [h] (let [w (cw)
            hd? (instance? Handle h)
            x (if hd? (aget ^objects (.-cell ^Handle h) 0) h)]
        (when (and w hd? (not (identical? w (.-w ^Handle h))) (not (inherited? w x)))
          (throw (lineage-ex x)))
        (if w (rv w x) x)))

(defn- debtor-row [w type size owner key at handles]
  (let [x (rw/new-row (g w rw/W-EPOCH) (g w rw/ID) size)]
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
    (s! c rw/C-RUNS 0)
    (register! w c)))

(defn- find-created
  "The index of the row with the positional creation `key` in list `l`;
   keyed rows (vector keys, Z#82) never match."
  [w l key]
  (when l
    (loop [i 0]
      (when (< i (acount l))
        (let [k (g (rv w (anth l i)) rw/KEY)]
          (if (and (number? k) (== (long key) (long k))) i (recur (inc i))))))))

(defn- effect-key!
  "§8.2: a registered effect's occurrence key, the site and a per-run
   ordinal of that site; never keyed. Shares R-ORD with positional
   creations by site. An ordinal below 2^20 is packed with its site into a
   long (site < 2^30: exact in JS doubles); a larger one, which would spill
   into the next site's range, is the pair [site ordinal], so keys stay
   distinct however long a run's effect loop is."
  [r site]
  (let [ords (or (gm r rw/R-ORD) (let [m (hs/vmap)] (s! r rw/R-ORD m) m))
        ord (long (or (hs/mget ords site) 0))]
    (hs/mput! ords site (inc ord))
    (if (< ord 1048576)
      (+ (* (long site) 1048576) ord)
      [site ord])))

(defn- creation-key!
  "§5.2 (Z#82): the creation key of a creation at `site` in run `r`.
   Inside `with-key` it is [site K n], `n` counting the run's earlier
   creations with the same site and keys K; otherwise the positional
   (site, n) packed into a long, `n` below 2^20."
  [r site]
  (if-let [ks (g r rw/R-KEY)]
    (let [kord (or (g r rw/R-KORD) {})
          sk [site ks]
          n (long (get kord sk 0))]
      (s! r rw/R-KORD (assoc kord sk (inc n)))
      [site ks n])
    (do (when-let [ords (g r rw/R-ORD)]
          (when (<= 1048576 (long (or (hs/mget ords site) 0)))
            (throw (ex-info "too many creations at one site in one run (2^20); create them under with-key"
                            {:spindel/invalid ::too-many-creations :site site}))))
        (effect-key! r site))))   ; below 2^20: the packed long, decoded by restore-ordinals!

(defn with-key*
  "§5.2 (Z#82), the thunk form of `with-key`: calls `f` with `k` appended to
   the running run's keys, restored however `f` exits. Outside a body it
   calls `f` unkeyed."
  [k f]
  (if-let [r (active-run)]
    (let [prev (g r rw/R-KEY)]
      (s! r rw/R-KEY (conj (or prev []) k))
      (try (f) (finally (s! r rw/R-KEY prev))))
    (f)))

(defn- frame-of
  "§8.2 addresses: the creation keys of the entities that created `x`, and
   of `x` itself; [] for an entity the host created."
  [x]
  (or (g x (if (comp? x) rw/C-FRAME rw/K-FRAME)) []))

(defn- set-origin!
  "Records how `x` was created: its `frame` and the creating run `r`'s path."
  [x frame r]
  (if (comp? x)
    (do (s! x rw/C-FRAME frame) (s! x rw/C-PATH (g r rw/R-PATH)) (s! x rw/C-BIND (thread-frame)))
    (do (s! x rw/K-FRAME frame) (s! x rw/K-PATH (g r rw/R-PATH))))
  x)

(defn push-path!
  "§8.2 P1, entering `with-path`: appends `p` to the running run's path.
   Returns the path to restore at exit; nil outside a body."
  [p]
  (when-let [r (active-run)]
    (let [prev (g r rw/R-PATH)]
      (s! r rw/R-PATH (not-empty (into (or prev []) p)))
      [prev])))

(defn pop-path!
  "§8.2 P2, leaving `with-path`: restores the path `push-path!` returned."
  [saved]
  (when saved
    (when-let [r (active-run)]
      (s! r rw/R-PATH (nth saved 0)))))

(defn- reject!
  "Z#83: run `r`'s creation rejected `x`, a predecessor in the basis (the kept
   prefix of a restart from the body, T11): `x` joins the adoption basis, so
   T12 releases it and the next cut drops it, as a rejected predecessor of the
   adoption basis."
  [w r x]
  (commit! w [:reject (g r rw/ID) (g x rw/ID)])
  nil)

(defn- adopt!
  "The creation of `c` with `key` in run `r`, from its basis or its adoption
   basis, when `ok?` accepts it (kind, captures, path, initial state). A
   rejected candidate stays in the adoption basis: the model's fresh creation
   leaves its predecessor there (T1, T4, create-link), for T12 or the next
   cut; one from the basis moves there first (Z#83)."
  [w r c key ok?]
  (let [basis (or (gm c rw/C-BASIS) (let [l (alist)] (s! c rw/C-BASIS l) l))
        abk (when (vector? key) (g c rw/C-ADOPT-K))]
    (if (vector? key)
      ;; keyed (Z#82): the counts make the key new in the basis, except for
      ;; the prefix a restart from the body re-creates (C-KEPT-K)
      (if-let [x (some->> (get abk key) (rv w))]
        (when (ok? x)
          (s! c rw/C-ADOPT-K (not-empty (dissoc abk key)))
          (aadd! basis x)   ; the adoption reference moves to the basis
          x)
        (when-let [x (some->> (get (g c rw/C-KEPT-K) key) (rv w))]
          (s! c rw/C-KEPT-K (not-empty (dissoc (g c rw/C-KEPT-K) key)))
          (if (ok? x)
            x   ; it stays in the basis
            ;; it leaves the basis at T12 or the next cut (take-rejected!)
            (do (s! c rw/C-REJ (conj (or (g c rw/C-REJ) []) x))
                (reject! w r x)))))
      (let [bi (find-created w basis key)
            ab (gm c rw/C-ADOPT)
            ai (when-not bi (find-created w ab key))]
        (cond bi (let [x (rv w (anth basis bi))]
                   (if (ok? x)
                     x
                     (do (aput! basis bi (rv w (anth basis (dec (acount basis)))))
                         (apop! basis)
                         (aadd! (or ab (let [l (alist)] (s! c rw/C-ADOPT l) l)) x)   ; its reference moves along
                         (reject! w r x))))
              ai (let [x (rv w (anth ab ai))]
                   (when (ok? x)
                     (aput! ab ai (rv w (anth ab (dec (acount ab))))) (apop! ab)
                     (aadd! basis x)   ; the adoption reference moves to the basis
                     x)))))))

(declare admit-change! admitting host-sealed? host-released? sealed-ex)

(declare released-ex)

(defn- body-released!
  "C1 Q5/Q8 (user decision 2026-11-18, model root-shut on body paths): a
   released world takes no new work, also from a run still in its slice (a
   body that released its own world): a creation throws ::released before
   any item or state change."
  []
  (when (g (cw) rw/W-RELEASED) (throw (released-ex))))

(defn create-comp!
  "T3. `site` is a macro-time int, `inputs` the captured values."
  [site inputs body]
  (if-let [r (active-run)]
    (when (valid-run)
      (body-released!)
      (let [w (cw)
            c (rv w (g r rw/R-OF))
            ;; §5.2: first, so a rejected creation (the ordinal limit)
            ;; changes nothing: no effect index, id or registration
            key (creation-key! r site)]
        (if-not (comp? c)
          ;; Created by a task run: owned by the run scope, retained by demand.
          (let [at (next-at! r)
                child (set-origin! (new-comp! w (run-scope! w r) 0 at inputs body 0)
                                   (conj (frame-of c) key) r)]
            (aadd! (g w rw/W-RQ) child)
            (let [h (handle! w child)]
              (commit! w [:create-comp (g r rw/ID) (g child rw/ID) [:opaque-seq inputs] [:opaque body]])
              h))
          (let [child (adopt! w r c key comp?)
                at (next-at! r)]   ; after a [:reject] item (Z#83), which ticks nothing
            (if child
              (do (s! child rw/AT at)   ; adoption reuses the live handle, or makes one (Z#29)
                  ;; bindings are not inputs: the latest creation's frame, no rerun
                  (when (comp? child) (s! child rw/C-BIND (thread-frame)))
                  (when (comp? child)
                    (when-not (and (same-inputs? inputs (g child rw/C-INPUTS))
                                   (= (g r rw/R-PATH) (g child rw/C-PATH)))
                      ;; W#5: like a write to the rerun source; §8.2 P4 a new path
                      (s! child rw/C-INPUTS inputs)
                      (s! child rw/C-PATH (g r rw/R-PATH))
                      (s! child rw/C-BODY body)
                      (if (g child rw/C-IDLE)
                        (do (s! child rw/C-IDLE false) (s! child rw/C-VALIDITY nil)
                            (s! child rw/C-EPOCH (inc (gl child rw/C-EPOCH))))
                        (do (s! child rw/C-EPOCH (inc (gl child rw/C-EPOCH)))
                            (s! child rw/C-RESTART true)
                            (mark-from! w child)
                            (maybe-schedule! w child)))))
                  (do (commit! w [:create-comp (g r rw/ID) (g child rw/ID) [:opaque-seq inputs] [:opaque body]])
                      ;; the item first: its projection is the readoption itself; a new
                      ;; handle (a dead one replaced) follows as its own [:handle-new]
                      (handle! w child)))
              ;; A body creation gets the body's weak handle (Z#13): +1 in handle!
              (let [child (set-origin! (new-comp! w c key at inputs body 0) (conj (frame-of c) key) r)]
                (aadd! (gm c rw/C-BASIS) child)
                (ref-inc! child)
                (let [h (handle! w child)]
                  (commit! w [:create-comp (g r rw/ID) (g child rw/ID) [:opaque-seq inputs] [:opaque body]])
                  h)))))))
    (let [w (or *world* (throw (ex-info "no world: bind v2/*world*" {})))
          h (top-handle w)
          fr (thread-frame)]             ; the caller's, before the item may move threads
      ;; C2: no new host work in a sealed world
      (admitting w
                 #(gated w
                         ;; admitted before T21, processed after it: refused, the handle
                         ;; stays unbound (its operations fail with ::released)
                         (if (host-released? w)
                           (refuse! w [:create-comp-top (g (rv w (g w rw/W-ROOT)) rw/ID) 0 [:opaque-seq inputs] [:opaque body]])
                           (let [c (new-comp! w (rv w (g w rw/W-ROOT)) 0 0 inputs body 1)]
                             (s! c rw/C-BIND fr)
                             (bind-handle! h c)
                             (aadd! (g w rw/W-RQ) c)   ; outside live: Rule R makes it idle (§3.4)
                             (commit! w [:create-comp-top (g (rv w (g w rw/W-ROOT)) rw/ID) (g c rw/ID) [:opaque-seq inputs] [:opaque body]])))))
      h)))

(defn- new-task! [w owner key at inputs body handles]
  (let [k (debtor-row w rw/T-TASK rw/K-SIZE owner key at handles)]
    (s! k rw/K-BODY body)
    ;; the captures are compared only to adopt a computation's task (§5.2);
    ;; elsewhere they are not kept (a running task would retain them, e.g. a
    ;; sequence head), except in verify mode for the projection
    (s! k rw/K-INPUTS (when (or (comp? owner) (logging? w)) inputs))
    (s! k rw/K-DONE false)
    (register! w k)))

(defn- start-task!
  "A task's run, starting from `frame` (its creator's bindings)."
  [w k frame]
  (let [r (new-run! w k 0)]
    (s! r rw/R-BIND frame)
    (aadd! (g w rw/W-START) r)
    r))

(defn- fork-local-opt
  "The `task-with` options: only `:fork-local` is known (Z#77)."
  [opts]
  (when opts
    (when-let [bad (seq (remove #{:fork-local} (keys opts)))]
      (throw (invalid-op :task-with (str "task-with: unknown options " (vec bad)))))
    (boolean (:fork-local opts))))

(defn spawn!
  "T4. Inside a computation run the task is a creation in its basis,
   adopted by later runs (§5.2); inside a task run it is a structured child
   of the run scope (Q10); at top level it is owned by the root scope.
   `opts` (`task-with`): `{:fork-local true}` makes the task fork-local
   (Z#77), as is every task created under a fork-local scope; never inside
   a computation."
  ([site inputs body] (spawn! site inputs body nil))
  ([site inputs body opts]
   (if-let [r (active-run)]
     (when (valid-run)
       (body-released!)
       (let [w (cw)
             x (rv w (g r rw/R-OF))
             local (fork-local-opt opts)
             _ (when (and local (comp? x))
                 (throw (invalid-op :fork-local "a computation's tasks are never fork-local (Z#77)")))
             key (creation-key! r site)]   ; §5.2: first, a rejected creation changes nothing
         (if (comp? x)
           (let [old (adopt! w r x key #(and (task? %) (same-inputs? inputs (g % rw/K-INPUTS))
                                             (= (g r rw/R-PATH) (g % rw/K-PATH))))   ; §8.2 P4
                 at (next-at! r)]
             (if old
               (do (s! old rw/AT at)
                   (do (commit! w [:spawn (g r rw/ID) [:opaque body] (g old rw/ID) [:opaque-seq inputs]])
                      ;; the item first: its projection is the readoption itself; a new
                      ;; handle (a dead one replaced) follows as its own [:handle-new]
                       (handle! w old)))
               ;; changed captures or path: a fresh task; the predecessor stays
               ;; in the adoption basis and runs until T12 or the next cut (T4)
               (let [k (set-origin! (new-task! w x key at inputs body 0) (conj (frame-of x) key) r)]
                 (aadd! (gm x rw/C-BASIS) k)
                 (ref-inc! k)
                 (start-task! w k (thread-frame))
                 (let [h (handle! w k)]
                   (commit! w [:spawn (g r rw/ID) [:opaque body] (g k rw/ID) [:opaque-seq inputs]])
                   h))))
           (let [at (next-at! r)
                 s (current-scope! w r)
                 local (or local (boolean (g s rw/S-LOCAL)))   ; Z#77: K2 inheritance
                 k (set-origin! (new-task! w s 0 at inputs body 0) (conj (frame-of x) key) r)]
             (when local (s! k rw/K-LOCAL true))
             (hs/oset-add! (gm s rw/S-TASKS) (id-of k) k)
             (ref-inc! k)
             (start-task! w k (thread-frame))
             (let [h (handle! w k)]
               (commit! w (cond-> [:spawn (g r rw/ID) [:opaque body] (g k rw/ID) [:opaque-seq inputs]]
                            local (conj true)))
               h)))))
     (let [w (or *world* (throw (ex-info "no world: bind v2/*world*" {})))
           local (fork-local-opt opts)
           h (top-handle w)
           fr (thread-frame)]             ; the caller's, before the item may move threads
      ;; C2: no new host work in a sealed world
       (admitting w
                  #(gated w
                          (let [s (rv w (g w rw/W-ROOT))]
                           ;; admitted before T21, processed after it: refused, the handle
                           ;; stays unbound (its operations fail with ::released)
                            (if (host-released? w)
                              (refuse! w (cond-> [:spawn-top (g s rw/ID) [:opaque body] 0 [:opaque-seq inputs]]
                                           local (conj true)))
                              (let [k (new-task! w s 0 0 inputs body 1)]
                                (when local (s! k rw/K-LOCAL true))
                                (bind-handle! h k)
                                (hs/oset-add! (gm s rw/S-TASKS) (id-of k) k)
                                (ref-inc! k)
                                (start-task! w k fr)
                                (commit! w (cond-> [:spawn-top (g s rw/ID) [:opaque body] (g k rw/ID) [:opaque-seq inputs]]
                                             local (conj true))))))))
       h))))

;; ---------------------------------------------------------------------------
;; Idle validation (§3.4, R#3)

(defn- validate!
  "Idle `c` becomes live with restart edges when every debtor in its
   validity still has the recorded version (Z#24); otherwise it must run."
  [w c]
  (let [vs (g c rw/C-VALIDITY)
        ;; a fresh computation has no result to reactivate: its validity is not checked
        ok? (and (some? (g c rw/C-DONE-EPOCH))
                 (not= :invalid vs)
                 (every? (fn [[d ver]]
                           (let [d (rv w d)]
                             (when (and (comp? d) (g d rw/C-IDLE)) (validate! w d))
                             (and (== (long ver) (gl d rw/VERSION))
                                  (or (source? d) (live? d)))))
                         vs))]
    (s! c rw/C-IDLE false)
    (s! c rw/C-VALIDITY nil)
    (if (and ok? (some? (g c rw/C-DONE-EPOCH)))
      (let [ins (gm c rw/C-INS)]
        (doseq [[d ver at base] (when (sequential? vs) vs)]
          ;; Z#51: a final debtor whose version still matches keeps the value
          ;; valid but takes no edge (consumed, as T6/T10/Z#48)
          ;; I12: a live computation debtor may have been raised while `c`
          ;; was idle (I14): raise `c` above it as T6 does; a raise that
          ;; meets `c` again would close a cycle, so that edge is dropped
          (let [d (rv w d)]
            (when-not (or (final? d) (and (comp? d) (not (raise-rank! w c d))))
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

(declare start-realizer! empty-inputs)

(defn- demand!
  "Runs a demanded debtor that needs a run and is eligible (T6 demand). An
   unrealized pull link starts its realizer (C0)."
  [w d]
  (cond
    (comp? d)
    (do (when (g d rw/C-IDLE) (validate! w d))
        (when (and (needs-run? w d) (eligible? w d))
          (if (let [r (active-run)] (and r (identical? (cw) w) (g (rv w r) rw/R-SLICE)))
            ;; D0: a host operation of this world inside a slice (observe!,
            ;; value-async, pin!) leaves the world's one slice to the running
            ;; run; the demanded run is dispatched at the next drain step. An
            ;; await parks its run first (its slice is free), so it still runs
            ;; the debtor on the host stack (I10).
            (when-not (g d rw/C-QUEUED)
              (s! d rw/C-QUEUED true)
              (aadd! (g w rw/W-READY) d))
            (dispatch! w d))))
    (task? d) nil
    ;; a released world's root scope is closed: no realizer starts there
    (link? d) (when (and (zero? (gl d rw/VERSION)) (g d rw/X-OPEN) (nil? (g d rw/X-RTASK))
                         (some? (nth (g d rw/X-REALIZE) 0))
                         (g (rv w (g w rw/W-ROOT)) rw/S-OPEN))
                (start-realizer! w d))))

;; ---------------------------------------------------------------------------
;; Rule R (§3.3) by retention counts

(defn- demote!
  "§3.3 step 1.3: a computation outside `live`."
  [w c]
  (when-let [r (rv w (g c rw/C-RUN))]
    (cancel! w r ::cancelled)
    ;; a cancelled run that survives in cleanup must not count as current
    ;; (I10, Z#42); one that retired at the cancel (§3.3 step 1.2, before
    ;; this demotion) leaves nothing to make stale
    (when (and (current? c r) (identical? r (rv w (g c rw/C-RUN))))
      (s! c rw/C-EPOCH (inc (gl c rw/C-EPOCH)))))
  (let [ins (gm c rw/C-INS)
        validity (loop [acc []]
                   (if (pos? (acount ins))
                     (let [e (rv w (apop! ins))
                           d (rv w (g e rw/E-DEBTOR))
                           acc (conj acc [d (g e rw/E-SEEN) (g e rw/E-AT) (g e rw/E-BASE)])]
                       (unlink! w e)
                       (recur acc))
                     acc))]
    (let [rej (take-rejected! w c)]   ; Z#83: adoption rows, released as such
      (when-let [b (g c rw/C-BASIS)]
        (s! c rw/C-BASIS nil)
        (dotimes [i (acount b)]
          (let [x (rv w (anth b i))]
            (when (and (task? x) (rv w (g x rw/K-RUN))) (cancel! w (rv w (g x rw/K-RUN)) ::cancelled))
            (when (stream? x) (close-source! w x))   ; C0: like its tasks, inside this item
            (ref-dec! w x))))
      (release-adoption! w c)
      (doseq [x rej] (release-adopted! w (rv w x))))
    (s! c rw/C-PENDING 0)
    (if (or (some? (g c rw/C-DONE-EPOCH)) (pos? (gl c rw/HANDLES)))
      (do (s! c rw/C-IDLE true)
          ;; §3.4: an idle computation keeps no run; each of its runs still
          ;; in cleanup keeps it as a tombstone (§3.2, C-RUNS) until it retires
          (s! c rw/C-RUN nil)
          ;; Z#64: a dirty computation (its result is not for its current
          ;; epoch: invalidated, or re-demoted right after a failed
          ;; validation) is :invalid, never valid by an empty edge list
          ;; A fresh one (no result) takes it from the removed edges too
          ;; (§3.3); an edge that never consumed a version makes it fail (Z#24).
          (s! c rw/C-VALIDITY (if (and (or (nil? (g c rw/C-DONE-EPOCH))
                                           (== (gl c rw/C-DONE-EPOCH) (gl c rw/C-EPOCH)))
                                       (every? (comp some? second) validity))
                                validity
                                :invalid)))
      ;; a run in cleanup keeps it as a tombstone (§3.2); it goes at retirement
      (when (zero? (gl c rw/C-RUNS)) (unregister! w c)))))

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
                  ;; a run in cleanup keeps its computation as a tombstone (§3.2)
                  (when (and (g row rw/C-IDLE) (zero? (gl row rw/HANDLES)) (zero? (gl row rw/C-RUNS)))
                    (unregister! w row)))
              (task? row)
              (do
                ;; §3.3 step 1.2: a computation's running task outside live
                ;; (no creation list, edge or host wait retains it) is
                ;; cancelled; a handle admits only a completed task (§3.4)
                (when-not (g row rw/K-DONE)
                  (when-let [kr (rv w (g row rw/K-RUN))]
                    (let [o (rv w (g row rw/OWNER))]
                      (when (and o (comp? o)) (cancel! w kr ::cancelled)))))
                ;; a run in cleanup keeps its task as a tombstone; it goes at retirement
                (when (and (g row rw/K-DONE) (zero? (gl row rw/HANDLES)) (nil? (rv w (g row rw/K-RUN))))
                  (unregister! w row)))
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
      ;; a task's body runs once: the row lets go of it (and its captures,
      ;; e.g. a sequence head the body walks past)
      (let [body (g k rw/K-BODY)]
        (s! k rw/K-BODY nil)
        (slice! r #(body ok-k err-k))))))

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
      (let [[r0 ek ex] (pop-first! w cleanup)
            r (rv w r0)]                     ; an entry a fork inherited names a basis row
        (if (nil? ek)
          ;; T15 for a resource that joined at its cancel (Z#55): [z]
          (resource-ack! w r)
          (do (s! r rw/R-SLICE true)
              (commit! w [:finalize (g r rw/ID)])
              (slice! r #(ek ex))))
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

(defn- isolated!
  "Runs `(f)` for another caller on the processing thread: a throw is that
   caller's, reported here, never raised into the thread that drives the
   turn (an unrelated host operation, or the drainer)."
  [what f]
  (try (f)
       (catch #?(:clj Throwable :cljs :default) t (report! what t))))

(defn- run-callbacks!
  "Host callbacks run between items, on the processing thread (H3), each
   isolated. H2: each callback is a unit of the turn, so at most the
   remaining budget `n` of the queued ones run, oldest first, and the time
   slice (`slice` ticks from `t0`, none when 0) is checked between them as
   between other units. The rest stay queued ahead of later ones: a batch
   is split at a callback boundary, and the next turn's items and slices
   may run before its rest. Returns how many ran, nil for none."
  [w ^long n ^long slice ^long t0]
  (let [cbs (g w rw/W-CALLBACKS)
        k (min n (acount cbs))]
    (when (pos? k)
      (let [batch (hs/take-first! cbs k)]
        (loop [i 0]
          (if (and (< i k)
                   (or (zero? i) (not (and (pos? slice) (>= (- (hs/now) t0) slice)))))
            (let [[cb [v err?]] (rv w (anth batch i))]
              (isolated! "host callback" #(cb v err?))
              (recur (inc i)))
            (do (when (< i k) (hs/put-first! cbs batch i))
                i)))))))

(defn- ingress [w] (g w rw/W-INGRESS))

(declare activate-dormant! normalize! retire-local!)

(defn- first-entry!
  "Z#77: before anything else at a fork's first gate entry, the fork-local
   runs it inherited are retired (T28, F6)."
  [w]
  (when (g w rw/W-RETIRE) (retire-local! w)))

(defn- run-turn!
  "H2: processes ingress items and internal work up to the budget, or until
   the time slice has passed (checked between units, after the first).
   Returns true when work remains."
  [w]
  (s! w rw/W-DRAINING true)
  (first-entry! w)
  (let [unborn? (g w rw/W-UNBORN)
        budget (gl w rw/W-BUDGET)
        slice #?(:clj (gl w rw/W-SLICE) :cljs (g w rw/W-SLICE))
        t0 (if (pos? slice) (hs/now) 0)]
    ;; E4: an unborn instance commits host items only: its inherited work and
    ;; dormant resources wait for activate!
    (when (and (not unborn?) (or (g w rw/W-DORMANT) (g w rw/W-DISCHARGE))) (activate-dormant! w))
    (when (and (not unborn?) (g w rw/W-NORMALIZE)) (normalize! w))
    (try
      (loop [n budget unborn? unborn?]
        (if (or (zero? n)
                (and (pos? slice) (< n budget) (>= (- (hs/now) t0) slice)))
          true
          (if-let [item (hs/mpsc-poll! (ingress w))]
            ;; a queued item is another caller's: its throw is reported, not
            ;; raised into this turn's driver (an item run inline by its own
            ;; caller, ingress-body's fast and held paths, throws to that caller)
            (do (isolated! "host item" item) (recur (dec n) (and unborn? (g w rw/W-UNBORN))))
            (cond (and (not unborn?) (drain-step! w)) (recur (dec n) false)
                  :else (if-let [k (run-callbacks! w n slice t0)] (recur (- n (long k)) unborn?) false)))))
      (finally (finish-metadata! w) (maybe-finish-token! w) (s! w rw/W-DRAINING false)))))

(declare handoff! activate-dormant!)

(defn- take-after!
  "Under the gate: the child worlds released during this turn (E3)."
  [w]
  (let [l (g w rw/W-AFTER)]
    (when (pos? (acount l))
      (let [cs (acopy l)] (aclear! l) cs))))

(declare holding-gate?)

(defn- run-after!
  "After the gate is released: schedule the released children's drains, and
   run the after-gate actions (C1: completion callbacks, child acks), each
   isolated."
  [cs]
  (when cs
    (dotimes [i (acount cs)]
      (let [x (anth cs i)]
        (cond
          ;; still under an enclosing world's gate (a nested entry): the
          ;; action, and the handoff of a world (which can run its turn on
          ;; this thread), waits for that gate to be left too
          (holding-gate?) (aadd! (g (cw) rw/W-AFTER) x)
          (fn? x)
          (try (x)
               (catch #?(:clj Throwable :cljs :default) t (report! "after-gate action" t)))
          ;; a failed handoff skips none of the others
          :else (isolated! "handoff" #(handoff! x)))))))

(defn- process!
  "H2: try the gate; the winner runs a bounded turn, then hands off. The
   loser returns at once: the holder hands off after releasing the gate, and
   sees the loser's item (both are sequentially consistent accesses)."
  [w]
  (let [lk (g w rw/W-LOCK)]
    (when (hs/try-lock! lk)
      (let [prev (enter-world! w)]
        (try (run-turn! w)
             (finally (let [cs (take-after! w)]
                        (hs/unlock! lk) (leave-world! prev) (run-after! cs))
                      ;; also on a throw: a drainer that lost the gate relies
                      ;; on this handoff
                      (handoff! w)))))))

(defn- work-pending? [w]
  (or (not (hs/mpsc-empty? (ingress w)))
      (pos? (acount (g w rw/W-CALLBACKS)))
      (and (not (g w rw/W-UNBORN))          ; E4: an unborn instance's work waits
           (or (pos? (acount (g w rw/W-READY))) (pos? (acount (g w rw/W-RESUME)))
               (pos? (acount (g w rw/W-START))) (pos? (acount (g w rw/W-CLEANUP)))))))

(defn- handoff!
  "H2: after releasing the gate, queued work is never stranded: schedule the
   world's drainer when work remains and none is scheduled. The scheduling
   claim belongs to this submission until its runnable starts, once: an
   executor that refuses the runnable (or runs it and then throws) makes it
   run on a fresh thread (hs/execute-surely!), and a second start finds the
   claim taken, so it never clears a later submission's claim."
  [w]
  (let [sched (g w rw/W-SCHEDULED)]
    (when (and (work-pending? w) (hs/flag-cas! sched false true))
      (let [claim (hs/flag true)]
        (try
          (hs/execute-surely! (g w rw/W-EXEC)
                              (fn [] (when (hs/flag-cas! claim true false)
                                       (hs/flag-set! sched false)
                                       (process! w))))
          (catch #?(:clj Throwable :cljs :default) t
            ;; no thread could be started: give back a claim still ours
            (when (hs/flag-cas! claim true false) (hs/flag-set! sched false))
            (throw t)))))))

(defn released-ex [] (control-ex "world released" {:spindel/released true}))

(defn- shut-ex
  "The refusal of a host admission to `w`, whose admission is shut
   (`W-SHUT`): a savepoint basis is frozen (S1), an unpublished fork-effect
   child is released (§8.1 F7)."
  [w]
  (if (= :frozen (g w rw/W-SHUT))
    (ex-info "a savepoint basis is frozen: it is only forked (instantiate, consume)"
             {:spindel/invalid :frozen})
    (released-ex)))

(defn sealed-ex [] (control-ex "world sealed" {:spindel/sealed true}))

(defn- host-sealed?
  "C2 (§9, model F1): `w` is sealed and the operation is the host's, not an
   effect of a run of `w` (bodies and propagation continue after a seal)."
  [w]
  (and (hs/flag? (g w rw/W-SEALED)) (not (and (identical? w (cw)) (active-run)))))

(defn- admit-kind!
  "API misuse is refused to the caller at once when the handle's row is
   known (it is bound; kinds never change). An unbound handle (its creating
   item still queued) is checked in the item."
  [h op]
  (when-let [x (when (instance? Handle h) (aget ^objects (.-cell ^Handle h) 0))]
    (when-not (kind-ok? x op) (throw (invalid-op op (kind-msg op))))))

(defn- host-released?
  "C1 Q5/Q8 (model root-shut/host-shut): `w` was released and the operation
   is the host's. Host items are refused at admission after T21; one
   admitted before it but processed after it is refused in its item, except
   a run's own slice (Z#40: a finalizer may still write, deliver, post,
   release and close)."
  [w]
  (and (g w rw/W-RELEASED) (not (and (identical? w (cw)) (active-run)))))

(defn- host-shut?
  "A host source change refused in its item: sealed (C2) or released."
  [w]
  (or (host-sealed? w) (host-released? w)))

(defn- admit-change!
  "C2: a host source change or admission is refused at once in a sealed
   world. An item admitted before the seal but processed after it is
   refused in the item (no state change; a refused log entry)."
  [w]
  (when (host-sealed? w) (throw (sealed-ex))))

(defn- admitting
  "C2 (model: the seal check atomic with the enqueue): `(f)` enqueues (or
   runs) a host start of `w` after its seal check. The start counts as in
   flight from before the check until after the enqueue, and §9 quiescence
   waits for none in flight: a start that passed the check before a seal
   is visible to `merge!` (counted, queued, or running), and one after it
   sees the seal (both sides sequentially consistent)."
  [w f]
  (let [k (g w rw/W-ADMITTING)]
    (hs/kids-add! k 1)
    (try (admit-change! w) (f)
         (finally (hs/kids-add! k -1)))))

(defn- withdraw!
  "`(f)`, a withdrawal (unobserve, unawait): in a released world there is
   nothing left to withdraw (T21), so its refusal is not an error."
  [f]
  (try (f)
       (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) e
         (when-not (:spindel/released (ex-data e)) (throw e)))))

#?(:clj
   (defn- inline-turns?
     "D (H2): whether a host operation on this thread may run a turn inline.
      False on a thread inside `without-inline-turns` that holds no gate; a
      thread processing a world ignores the setting (H1, H4, B7)."
     []
     (let [c (ctx)]
       (or (nil? (aget c 3))
           (when-let [w (aget c 0)] (hs/held? (g w rw/W-LOCK)))))))

#?(:clj
   (defn without-inline-turns
     "D (H2): calls `(f)` with this JVM thread running no inline turns. A host
      operation it issues while holding no gate is enqueued and handed to the
      world's drainer, as on a world created with `:inline? false`, and
      returns what it returns there without waiting for the item (which may
      commit before or after the return): a bare host item nothing (its
      throw is reported by the processing thread), commands their usual
      value, creations unbound handles, `value-async`/`observe!`/
      `release-world!` their fns; `host-call!` clients wait for the reply,
      and an interrupt ends that wait while the item still runs later. An
      item admitted before a release commits is handled by its operation
      when it runs (spec H2). Dispatch isolation needs an executor that runs
      handoffs asynchronously. A thread inside a gate (a slice, an item or a
      callback) ignores the setting. Nests; the setting is the thread's, not a
      dynamic binding, so it never reaches a slice (B10)."
     [f]
     (let [c (ctx) prev (aget c 3)]
       (aset c 3 true)
       (try (f) (finally (aset c 3 prev))))))

#?(:clj
   (defmacro no-inline
     "D (H2): runs `body` with this JVM thread running no inline turns; see
      `without-inline-turns`."
     [& body]
     `(without-inline-turns (fn [] ~@body))))

#?(:clj
   (defmacro ingress-body
     "The body of host!/internal!: `admit?` is a literal, so the release
      check folds away for internal items. On the JVM a thread inside
      `without-inline-turns` that holds no gate takes the non-inline branch
      (D, H2)."
     [w f admit?]
     (let [w' (gensym "w") f' (gensym "f") lk (gensym "lk") prev (gensym "prev")
           v (gensym "v") l (gensym "l") cs (gensym "cs")
           inline (if (rw/cljs? &env)
                    `(g ~w' rw/W-INLINE)
                    `(and (g ~w' rw/W-INLINE) (inline-turns?)))]
       `(let [~w' ~w ~f' ~f ~lk (g ~w' rw/W-LOCK)]
          (cond
            ~@(cond
                (true? admit?)
                [`(and (g ~w' rw/W-RELEASED) (not (and (identical? ~w' (cw)) (active-run))))
                 `(throw (released-ex))
                 `(and (g ~w' rw/W-SHUT) (not (and (identical? ~w' (cw)) (active-run))))
                 `(throw (shut-ex ~w'))]
                (false? admit?) []
                :else
                [`(and ~admit? (g ~w' rw/W-RELEASED) (not (and (identical? ~w' (cw)) (active-run))))
                 `(throw (released-ex))
                 `(and ~admit? (g ~w' rw/W-SHUT) (not (and (identical? ~w' (cw)) (active-run))))
                 `(throw (shut-ex ~w'))])
            (hs/held? ~lk) (if (identical? ~w' (cw))
                             (~f')
                             (let [~prev (enter-world! ~w')]
                               (try (first-entry! ~w') (~f') (finally (leave-world! ~prev)))))
            ;; Fast path: nothing queued and the gate is free, so running the
            ;; item now keeps FIFO order without an ingress node.
            (and ~inline (hs/mpsc-empty? (ingress ~w')) (hs/try-lock! ~lk))
            (let [~prev (enter-world! ~w')
                  ~v (try (s! ~w' rw/W-DRAINING true)
                          (let [~v (try (first-entry! ~w') (~f') (finally (s! ~w' rw/W-DRAINING false)))]
                            (run-turn! ~w')
                            ~v)
                          (finally
                            (let [~l (g ~w' rw/W-AFTER)]
                              (if (zero? (acount ~l))
                                (do (hs/unlock! ~lk) (leave-world! ~prev))
                                (let [~cs (take-after! ~w')]
                                  (hs/unlock! ~lk) (leave-world! ~prev) (run-after! ~cs))))
                            ;; also when the item throws: a drainer that lost
                            ;; the gate meanwhile relies on this handoff (H2)
                            (handoff! ~w')))]
              ~v)
            :else
            (do (hs/mpsc-add! (ingress ~w') ~f')
                (if ~inline (process! ~w') (handoff! ~w'))
                nil))))))

(defn- ingress* [w f admit?]
  (ingress-body w f admit?))

(defn host!
  "H1: a host operation `f` of world `w`. A thread that already holds the
   world (inside a slice or a callback) runs it at once; any other thread
   enqueues it, then tries the gate (H2) unless the world is not inline. A
   released world refuses host operations (T21), except the effects of a
   run's own slice: a finalizer of a cleanup entry may still deliver, post,
   release and write (Z#40, Z#56)."
  [w f]
  (ingress* w f true))

(defn- internal!
  "A completion of an outstanding resource: not an admission, so it is
   accepted after release and joins (T21, L2)."
  [w f]
  (ingress* w f false))

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
  (let [l (or (gm sc rw/S-SOURCES) (let [l (alist)] (s! sc rw/S-SOURCES l) (s! sc rw/S-PRUNE 8) l))]
    (aadd! l (hs/weak x))
    (when (> (acount l) (gl sc rw/S-PRUNE))
      (let [live (alist)]
        (dotimes [i (acount l)]
          (let [r (rv w (anth l i))] (when (hs/deref-weak r) (aadd! live r))))
        (s! sc rw/S-SOURCES live)
        (s! sc rw/S-PRUNE (max 8 (* 2 (acount live))))))))

(declare end-stream!)

(defn- close-source!
  "A closed source is final and read-only (T16, R#15): its dep edges are
   removed after their current delivery (T10). A stream ends its tail first:
   its readers get the end (C0)."
  [w x]
  (when (g x rw/X-OPEN)
    (when (stream? x) (end-stream! w x nil))
    (s! x rw/X-OPEN false)
    (settle! w x)))

(defn- source-item-value
  "A creation item's initial value: opaque (interned in the log), except a
   semaphore's permit count, which the model compares against its maximum
   (Z#62), and a mailbox's, which is not a value (nil)."
  [kind v]
  (cond (== kind rw/SRC-SEMAPHORE) v
        (== kind rw/SRC-MAILBOX) [:opaque nil]
        :else [:opaque v]))

(defn- create-source-in-run!
  "T1 inside a run: owned by the computation (in its basis, adopted by later
   runs by creation key, §5.2) or by the task run's current scope, which retains
   it only through edges and handles (§5.2)."
  [r kind v init]
  (body-released!)
  (let [w (cw)
        x (rv w (g r rw/R-OF))
        ;; §5.2: first, a rejected creation changes nothing
        key (when (comp? x) (creation-key! r -1))]
    (if (comp? x)
      ;; readoption by creation key needs the same kind (a run that creates a
      ;; signal where the last one created a mailbox makes a new source; the
      ;; other stays in the adoption basis)
      (let [old (adopt! w r x key #(and (source? %) (== (long kind) (gl % rw/X-KIND))))
            at (next-at! r)]
        (if old
          (do (s! old rw/AT at)
              (do (commit! w [:create-source (g r rw/ID) (rw/kind-names kind)
                              (source-item-value kind v) (g old rw/ID)])
                  ;; the item first: its projection is the readoption itself; a new
                  ;; handle (a dead one replaced) follows as its own [:handle-new]
                  (handle! w old)))
          (let [s (new-source! w kind v x key at)]
            (s! s rw/HANDLES 0)
            (when init (init s))
            (aadd! (gm x rw/C-BASIS) s)
            (ref-inc! s)
            (let [h (handle! w s)]
              (commit! w [:create-source (g r rw/ID) (rw/kind-names kind)
                          (source-item-value kind v) (g s rw/ID)])
              h))))
      (let [at (next-at! r)
            sc (current-scope! w r)
            s (new-source! w kind v sc 0 at)]
        (own-source! w sc s)
        (s! s rw/HANDLES 0)
        (when init (init s))
        (aadd! (g w rw/W-RQ) s)
        (let [h (handle! w s)]
          (commit! w [:create-source (g r rw/ID) (rw/kind-names kind)
                      (source-item-value kind v) (g s rw/ID)])
          h)))))

(defn- create-source-top! [w kind v init]
  (if-let [r (active-run)]
    (if (valid-run) (create-source-in-run! r kind v init) (throw (ex-info "source creation in a cancelled run" {})))
    (create-source-top-host! w kind v init)))

(defn- create-source-top-host! [w kind v init]
  (let [h (top-handle w)]
    (gated w
           ;; admitted before T21, processed after it: refused (model root-shut),
           ;; the handle stays unbound
           (if (host-released? w)
             (refuse! w [:create-source-top (g (rv w (g w rw/W-ROOT)) rw/ID)
                         (rw/kind-names kind)
                         (source-item-value kind v) 0])
             (let [x (new-source! w kind v (rv w (g w rw/W-ROOT)) 0 0)]
               (when init (init x))
               (bind-handle! h x)
               (commit! w [:create-source-top (g (rv w (g w rw/W-ROOT)) rw/ID)
                           (rw/kind-names kind)
                           (source-item-value kind v) (g x rw/ID)]))))
    h))

(defn signal
  "T1 at top level: a signal in `w` (default `*world*`)."
  ([v] (signal *world* v))
  ([w v] (create-source-top! w rw/SRC-SIGNAL v nil)))

(defn- mailbox? [x] (== rw/SRC-MAILBOX (gl x rw/X-KIND)))

(defn- deque [x i] (gm x i))   ; every use mutates or polls

(defn- available? [x]
  (if (mailbox? x)
    (not (hs/dq-empty? (deque x rw/X-VALUE)))
    (pos? (gl x rw/X-VALUE))))

(defn- consume! [x]
  (if (mailbox? x)
    (hs/dq-poll! (deque x rw/X-VALUE))
    (do (s! x rw/X-VALUE (dec (gl x rw/X-VALUE))) :acquired)))

(defn consume-effect!
  "`take!` (mailbox) or `acquire!` (semaphore): a consuming operation, always
   a wait edge, never a dependency (§4.3). Waiters are served FIFO."
  [x k ek]
  (if-let [refusal (or (when-not (kind-ok? (row-of x) :take) (invalid-op :take (kind-msg :take)))
                       (unwinding-finalizer-refusal) (when-not (let [x (row-of x)] (or (available? x) (closed? x))) (finalizer-refusal)))] (ek refusal)
          (if-let [r (valid-run)]
            (let [w (cw)
                  at (next-at! r)
                  aid (alloc-id! w)]
              (cond
                (available? x)
                (let [v (consume! x)]
                  (alloc-id! w)                             ; the consumed wait edge
                  (s! x rw/VERSION (inc (gl x rw/VERSION)))
                  (commit! w [:take (g r rw/ID) (g x rw/ID) [:opaque k] aid])
                  (k v))
        ;; Z#57: closed and empty, nothing can arrive: fail at once, like a
        ;; waiter woken by the close (Z#53)
                (closed? x)
                (do (alloc-id! w)                           ; the consumed wait edge
                    (commit! w [:take (g r rw/ID) (g x rw/ID) [:opaque k] aid])
                    (ek (closed-ex)))
                :else
                (let [members (object-array 1)
                      a (new-activation! w aid r :one k ek members (object-array 1) 1)
                      e (link! w rw/EK-WAIT a x at)]
                  (aset members 0 e)
                  (hs/dq-push! (deque x rw/X-WAITERS) e)
                  (park! r a)
                  (s! a rw/A-INLINE false)
                  (commit! w [:take (g r rw/ID) (g x rw/ID) [:opaque k] aid])
                  (notify-blocked! (rv w (g r rw/R-OF)) 0)
                  nil)))
            (unwind! ek))))

(defn- serve-waiter!
  "The first waiter whose activation can still receive gets `v`. Waiters of
   stale or cancelled runs are skipped (§4.5.4)."
  [w x v]
  (let [q (deque x rw/X-WAITERS)]
    (loop []
      (when-let [e (rv w (hs/dq-poll! q))]   ; this world's copy of an inherited waiter
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
  (admit-kind! h :post)
  (admit-change! (world-of h))
  (gated (world-of h)
         (let [x (row-of h) w (cw)]
           (if (or (closed? x) (not (kind-ok? x :post)) (host-shut? w))
             (refuse! w [:post (g x rw/ID) [:opaque v]])
             (do (s! x rw/VERSION (inc (gl x rw/VERSION)))
                 (when-not (serve-waiter! w x v)
                   (hs/dq-push! (deque x rw/X-VALUE) v))
                 (when-not (gone? w x) (commit! w [:post (g x rw/ID) [:opaque v]]))))))
  nil)

(defn semaphore
  "T1 at top level: a counting semaphore with `n` permits (§4.3)."
  ([n] (semaphore *world* n))
  ([w n]
   (when-not (pos? n)
     (throw (ex-info "a semaphore needs a positive permit count" {:spindel/invalid :semaphore :permits n})))
   (create-source-top! w rw/SRC-SEMAPHORE (long n)
                       #(do (s! % rw/X-WAITERS (hs/deque)) (s! % rw/X-MAX (long n))))))

(defn sem-release!
  "Gives the permit to the first armed waiter, or returns it (§4.3). A
   release at the maximum is refused and throws (Z#62, old over-release)."
  [h]
  (admit-kind! h :release)
  (admit-change! (world-of h))
  (let [over? (host-call! (world-of h)
                          #(let [x (row-of h) w (cw)]
                             (cond
                               (or (closed? x) (not (kind-ok? x :release))) (do (refuse! w [:release (g x rw/ID)]) false)
                               (host-shut? w) (do (refuse! w [:release (g x rw/ID)]) false)
                               (and (some? (g x rw/X-MAX)) (>= (gl x rw/X-VALUE) (gl x rw/X-MAX)))
                               (do (refuse! w [:release (g x rw/ID)]) true)
                               :else
                               (do (s! x rw/VERSION (inc (gl x rw/VERSION)))
                                   (when-not (serve-waiter! w x :acquired)
                                     (s! x rw/X-VALUE (inc (gl x rw/X-VALUE))))
                                   (when-not (gone? w x) (commit! w [:release (g x rw/ID)]))
                                   false))))]
    (when over?
      (throw (ex-info "release beyond the semaphore's maximum" {:spindel/invalid :over-release}))))
  nil)

(defn permits
  "The available permits of a semaphore (old @semaphore)."
  [h]
  (let [w (world-of h)]
    (host-call! w #(g (row-of h) rw/X-VALUE))))

(defn deferred
  "T1 at top level: a deferred, delivered once (§4.3)."
  ([] (deferred *world*))
  ([w] (create-source-top! w rw/SRC-DEFERRED nil nil)))

(defn deliver!
  "Delivers a deferred once: fires its edges and finalizes it (§4.3, T10).
   A second delivery is refused."
  [h v]
  (admit-kind! h :deliver)
  (admit-change! (world-of h))
  (gated (world-of h)
         (let [x (row-of h) w (cw)]
           (if (or (final? x) (not (kind-ok? x :deliver)) (host-shut? w))
             (refuse! w [:deliver (g x rw/ID) [:opaque v]])
             (do (s! x rw/X-VALUE v)
                 (s! x rw/VERSION 1)
                 (settle! w x)
                 (when-not (gone? w x) (commit! w [:deliver (g x rw/ID) [:opaque v]]))))))
  v)

;; ---------------------------------------------------------------------------
;; Async sequences (C0, .internal/c-async-seq-design.md): a sequence is a
;; chain of links, once-cells delivered with [v next-position], nil (the end)
;; or a memoized error. A position is a link's handle. Links are owned by the
;; root scope (never closed by a run's retirement); a pull link is realized
;; by a root task started when it is first demanded, at most once per world.

(defn- new-link!
  "A link in `w`'s root scope, returned as its handle (a position): the top
   handle `top` when given, else a new one. `spec` is [f s frame stream-id
   index] (f nil for a push link; stream-id nil: the link's own ID). It is
   retained by its positions and the chain that reaches it. It makes no
   item: the operation that creates it commits it (C0, one item each)."
  [w spec top]
  (let [x (new-source! w rw/SRC-LINK nil (rv w (g w rw/W-ROOT)) 0 0)
        spec (if (nil? (nth spec 3)) (assoc spec 3 (g x rw/ID)) spec)]
    (s! x rw/X-REALIZE spec)
    (if top (do (bind-handle! top x) top) (do (s! x rw/HANDLES 0) (handle! w x)))))

(defn- handle-id [h] (g (aget ^objects (.-cell ^Handle h) 0) rw/ID))

(defn- start-realizer!
  "Demand on an unrealized pull link (C0 V1): a task owned by the root scope
   runs `(f s)` with the creation bindings (B10); its completion realizes
   the link (link-done!). A reader's cancellation does not cancel it."
  [w x]
  (let [[f s frame] (g x rw/X-REALIZE)
        root (rv w (g w rw/W-ROOT))
        body (fn [ok err] ((f s) ok err))
        k (new-task! w root 0 0 empty-inputs body 0)]
    (s! k rw/K-LINK x)
    (hs/oset-add! (gm root rw/S-TASKS) (id-of k) k)
    (ref-inc! k)
    (s! x rw/X-RTASK k)
    (start-task! w k frame)
    (commit! w [:link-demand (g x rw/ID) (g k rw/ID)])
    k))

(defn- realize!
  "Delivers link `x` once with `value` ([v next-handle], nil or a Failure)
   and fires its readers, inside the caller's item. Its realizer state goes
   (the next link carries the next state), except for a computation's head,
   kept for adoption (V4)."
  [w x value]
  (let [spec (g x rw/X-REALIZE)]
    (when (and (nth spec 0) (< (count spec) 6))
      (s! x rw/X-REALIZE [nil nil nil (nth spec 3) (nth spec 4)])))
  (s! x rw/X-VALUE value)
  (s! x rw/VERSION 1)
  (settle! w x))

(defn- link-done!
  "After the realizer of `x` completed (its T12 item) with `res`: [v s'] →
   the next link; nil → the end; an error → memoized (also a cancellation
   its body propagated), except ::forked (V2), which leaves the link
   unrealized and restarts it when it is demanded. One item:
   [:link-realize x tag v next] (tag 1 value, 0 end, 2 error; next 0 when
   none). A link nothing reaches any more (no position, no reader) is left
   alone: nobody can read it."
  [w x res err?]
  (s! x rw/X-RTASK nil)
  (when (and (zero? (gl x rw/VERSION)) (g x rw/X-OPEN)
             (or (pos? (gl x rw/REFS)) (pos? (gl x rw/HANDLES)))
             (g (rv w (g w rw/W-ROOT)) rw/S-OPEN))    ; no root-owned link after release
    (let [fail (fn [e] (realize! w x (Failure. e))
                 (commit! w [:link-realize (g x rw/ID) 2 [:opaque e] 0]))]
      (cond
        (and err? (:spindel/forked (ex-data res)))
        (when (hot? x) (start-realizer! w x))
        err? (fail res)
        (nil? res) (do (realize! w x nil)
                       (commit! w [:link-realize (g x rw/ID) 0 [:opaque nil] 0]))
        (and (vector? res) (== 2 (count res)))
        (let [[f _ frame sid i] (g x rw/X-REALIZE)
              nh (new-link! w [f (nth res 1) frame sid (inc (long i))] nil)]
          (realize! w x [(nth res 0) nh])
          (commit! w [:link-realize (g x rw/ID) 1 [:opaque (nth res 0)] (handle-id nh)]))
        :else
        (fail (ex-info "an aseq step returns [value next-state] or nil"
                       {:spindel/invalid :aseq :result res}))))))

(defn- link-cancelled!
  "The realizer of `x` was cancelled (world release, T21): nothing is
   realized; no item."
  [x]
  (s! x rw/X-RTASK nil))

(defn new-aseq
  "A pull sequence from state `init`: `(f s)` returns a body whose value is
   `[v s']` or nil (the end). Returns its head position. Use the `aseq`
   macro. Item: [:create-link run link] in a body, [:create-link-top root
   link] on the host."
  ([f init] (new-aseq f init nil))
  ([f init id]
   (if-let [r (active-run)]
     (when (valid-run)
       (body-released!)
       (next-at! r)
       (let [w (cw) h (new-link! w [f init (thread-frame) id 0] nil)]
         (commit! w [:create-link (g r rw/ID) (handle-id h)])
         h))
     (let [w (or *world* (throw (ex-info "no world: bind v2/*world*" {})))
           h (top-handle w)
           fr (thread-frame)]
       (gated w
              ;; admitted before T21, processed after it: refused (root-shut)
              (if (host-released? w)
                (refuse! w [:create-link-top (g (rv w (g w rw/W-ROOT)) rw/ID) 0])
                (do (new-link! w [f init fr id 0] h)
                    (commit! w [:create-link-top (g (rv w (g w rw/W-ROOT)) rw/ID) (handle-id h)]))))
       h))))

(defn new-aseq-at
  "`new-aseq` at creation site `site` with the captured `inputs` (the `aseq`
   macro). In a computation run the sequence is a creation in its basis: a
   re-entry with the same captures and initial state adopts it (V4), so its
   readers keep the realized elements; otherwise it is a new sequence. The
   item is [:create-link run link], with the adopted link's id on adoption."
  [site inputs f init]
  (let [r (active-run)
        x (when r (rv (cw) (g r rw/R-OF)))]
    (if-not (and x (comp? x))
      (new-aseq f init)
      (when (valid-run)
        (body-released!)
        (let [w (cw)
              key (creation-key! r site)   ; §5.2: first, a rejected creation changes nothing
              old (adopt! w r x key #(when (link? %)
                                       (let [spec (g % rw/X-REALIZE)]
                                         (and spec (same-inputs? inputs (nth spec 5))
                                              (same-capture? init (nth spec 1))))))
              at (next-at! r)]
          (if old
            (do (s! old rw/AT at)
                (do (commit! w [:create-link (g r rw/ID) (g old rw/ID)])
                    ;; the item first: its projection is the readoption itself; a new
                    ;; handle (a dead one replaced) follows as its own [:handle-new]
                    (handle! w old)))
            ;; other captures or initial state: a new link; the predecessor
            ;; stays in the adoption basis until T12 or the next cut
            (let [h (new-link! w [f init (thread-frame) nil 0 inputs] nil)
                  nx (row-of h)]
              (s! nx rw/KEY key)
              (s! nx rw/AT at)
              (aadd! (gm x rw/C-BASIS) nx)
              (ref-inc! nx)
              (commit! w [:create-link (g r rw/ID) (g nx rw/ID)])
              h)))))))

(defn stream
  "A push stream (C0): `append!` adds elements, `close!` ends it, and it ends
   when the scope that created it closes (Z#18: a task's stream at the task's
   retirement) or, created in a computation, when it leaves the
   computation's basis. Readers hold positions: `(position s)` is the
   current tail. `:id` names it for portable positions (C3); default its row
   ID. Its first tail link is part of the creation item (ID = stream ID + 1)."
  ([] (stream *world* nil))
  ([w-or-opts] (if (map? w-or-opts) (stream *world* w-or-opts) (stream w-or-opts nil)))
  ([w {:keys [id]}]
   (create-source-top! w rw/SRC-STREAM nil
                       (fn [x] (s! x rw/X-VALUE (new-link! (cw) [nil nil nil (or id (g x rw/ID)) 0] nil))))))

(defn- end-stream!
  "Realizes the stream's tail as the end, or with the error `err`, inside the
   caller's item."
  [w x err]
  (let [t (row-of (g x rw/X-VALUE))]
    (when (zero? (gl t rw/VERSION))
      (realize! w t (when err (Failure. err))))))

(defn append!
  "Appends `v` to stream `h`: one item [:append s v new-tail] creates the new
   tail, realizes the old one with [v new-tail] and fires its readers.
   Refused on a closed stream."
  [h v]
  (admit-change! (world-of h))
  (gated (world-of h)
         (let [x (row-of h) w (cw)]
           (cond
             (not (stream? x)) (throw (invalid-op :append "append! is for streams"))
             (host-shut? w) (refuse! w [:append (g x rw/ID) [:opaque v] 0])
             ;; a released world's root scope is closed: no new root-owned
             ;; link (an append from a cleanup finalizer is refused like one
             ;; to a closed stream)
             (or (closed? x) (not (g (rv w (g w rw/W-ROOT)) rw/S-OPEN)))
             (refuse! w [:append (g x rw/ID) [:opaque v] 0])
             :else
             (let [t (row-of (g x rw/X-VALUE))
                   [_ _ _ sid i] (g t rw/X-REALIZE)
                   nh (new-link! w [nil nil nil sid (inc (long i))] nil)]
               (s! x rw/X-VALUE nh)
               (s! x rw/VERSION (inc (gl x rw/VERSION)))
               (realize! w t [v nh])
               (commit! w [:append (g x rw/ID) [:opaque v] (handle-id nh)])))))
  nil)

(defn close!
  "Ends stream `h`: its readers reach the end, or the error `err`. One item
   [:close s tag v] (tag 0 end, 2 error)."
  ([h] (close! h nil))
  ([h err]
   (admit-change! (world-of h))
   (gated (world-of h)
          (let [x (row-of h) w (cw)]
            (when-not (stream? x) (throw (invalid-op :close "close! is for streams")))
            (if (host-shut? w)
              (refuse! w [:close (g x rw/ID) (if err 2 0) [:opaque err]])
              (when (g x rw/X-OPEN)
                (end-stream! w x err)
                (close-source! w x)
                (when-not (gone? w x) (commit! w [:close (g x rw/ID) (if err 2 0) [:opaque err]]))))))
   nil))

(defn position
  "The current tail of stream `h`: a reader there sees what is appended
   after (and, once the stream ends, the end)."
  [h]
  (host-call! (world-of h) #(let [x (row-of h)]
                              (when-not (stream? x) (throw (invalid-op :position "position is for streams")))
                              (g x rw/X-VALUE))))

(defn ready?
  "Whether position `h` is realized, so awaiting it returns at once. Never
   demands it."
  [h]
  (host-call! (world-of h) #(let [x (row-of h)]
                              (when-not (link? x) (throw (invalid-op :ready? "ready? is for positions")))
                              (pos? (gl x rw/VERSION)))))

(defn position-id
  "The portable name [stream-id index] of position `h` (C3)."
  [h]
  (host-call! (world-of h) #(let [[_ _ _ sid i] (g (row-of h) rw/X-REALIZE)] [sid i])))

(defn- notify-watches!
  "Snapshot under the world gate; callbacks run without metadata locks."
  [w id ref old new]
  (doseq [[k f] (lt/callbacks (g w rw/W-WATCHES) id)]
    (try (f k ref old new)
         (catch #?(:clj Throwable :cljs :default) t
           #?(:clj (binding [*out* *err*] (println "watch" k "failed:" t))
              :cljs (js/console.error "watch" k "failed:" t))))))

(defn- write-row!
  "T2 on the open source row `x` of `w`; `ref` is what its watches receive.
   `ds` are the write's deltas, nil when unknown (§4.4)."
  ([w x ref v] (write-row! w x ref v nil))
  ([w x ref v ds]
   (let [old (g x rw/X-VALUE)
         ver (inc (gl x rw/VERSION))]
     (s! x rw/X-VALUE v)
     (s! x rw/VERSION ver)
     (log-deltas! x ver ds)
     (let [outs (acopy (g x rw/OUTS))]
       (dotimes [i (acount outs)]
         (let [e (rv w (anth outs i)) k (gl e rw/E-KIND)]
           (cond (== k rw/EK-DEP) (fire-dep! w e)
                 (== k rw/EK-OBSERVE) (deliver-observe! w e)))))
     (when-not (gone? w x) (commit! w [:write (g x rw/ID) [:opaque v]]))
     (notify-watches! w (g x rw/ID) ref old v))))

(defn- write-d!
  "T2 with the write's deltas (nil when unknown)."
  [h v ds]
  (admit-kind! h :write)
  (admit-change! (world-of h))
  (gated (world-of h)
         (let [x (row-of h) w (cw)]
           (if (or (closed? x) (not (kind-ok? x :write)) (host-shut? w))
             (refuse! w [:write (g x rw/ID) [:opaque v]])
             (write-row! w x h v ds))))
  v)

(defn write!
  "T2: `version += 1`, fire dep edges and deliver observe edges (§4.5.1).
   A plain write carries no deltas."
  [h v]
  (write-d! h v nil))

(defn rerun!
  "§4.1: a write to the rerun source of computation `h` (old `rerun!`,
   `mark-dirty!`). Its next run starts from the body. A live computation is
   invalidated at once (an epoch step, marking its creditors) and runs again
   if demanded; an idle one becomes invalid and runs when next demanded.
   Throws for a handle that is not a computation."
  [h]
  (host-call! (world-of h)
              #(let [c (row-of h) w (cw)]
                 (when-not (comp? c)
                   (throw (invalid-op :rerun "rerun! is for computations")))
                 (if (g c rw/C-IDLE)
                   (s! c rw/C-VALIDITY :invalid)
                   (do (s! c rw/C-EPOCH (inc (gl c rw/C-EPOCH)))
                       (s! c rw/C-RESTART true)
                       (mark-from! w c)
                       (maybe-schedule! w c)))
                 (commit! w [:rerun (g c rw/ID)])
                 nil)))

(defn unborn-ex []
  (control-ex "instance not activated: only writes before activate! (S3)" {:spindel/unborn true}))

(defn- calling-frame
  "Marks the caller of a host operation, so its item can tell whether it runs
   while that caller is still waiting on it (JVM: the caller's thread)."
  []
  #?(:clj (Thread/currentThread) :cljs (volatile! true)))

(defn- in-calling-frame? [m]
  #?(:clj (identical? m (Thread/currentThread)) :cljs @m))

(defn- leave-calling-frame! [m]
  #?(:clj nil :cljs (vreset! m false)))

(defn- shut-roots!
  "T21/Z#40/Z#68: a released world takes no new root. Host items are refused
   at ingress, but a cleanup slice may still run host operations of its own
   world (Z#40: write, deliver, post, release, close); an observe or a pin
   from there would add a root after T21 revoked them, and a computation it
   demands could run after the world completed. The refusal throws to a
   caller still waiting on the operation (`m`, its calling frame). An item
   admitted before T21 but processed after it, in a turn another thread
   drains, is revoked as T21 revokes roots instead (true): its observe
   callback receives ::released, its pin is dropped. Thrown there, the
   refusal would reach the draining thread, not the caller."
  [w m]
  (when (g w rw/W-RELEASED)
    (if (in-calling-frame? m) (throw (released-ex)) true)))

(defn observe!
  "T8: `cb` receives (value err?) on each change. Returns an unobserve fn."
  [h cb]
  (let [w (world-of h)
        ev (volatile! nil)
        m (calling-frame)]
    (when (g w rw/W-UNBORN) (throw (unborn-ex)))
    (admit-change! w)
    (try
      (gated w
             (cond
               (shut-roots! w m)
               (aadd! (g w rw/W-CALLBACKS) [cb [(released-ex) true]])
               ;; C2: sealed meanwhile (admitted before the seal)
               (host-sealed? w)
               (aadd! (g w rw/W-CALLBACKS) [cb [(sealed-ex) true]])
               :else
               (let [d (row-of h)]
                 (if (stream? d)
                   ;; a stream is read through its positions (as value-async, C0)
                   (aadd! (g w rw/W-CALLBACKS) [cb [(stream-ex) true]])
                   (let [e (link! w rw/EK-OBSERVE cb d 0)]
                     (vreset! ev e)
                     (when (and (comp? d) (g d rw/C-IDLE)) (validate! w d))
                     (deliver-observe! w e)
                     (commit! w [:observe (g d rw/ID) [:opaque cb] (g e rw/ID)])
                     (demand! w d))))))
      (finally (leave-calling-frame! m)))
    (fn []
      (withdraw!
       (fn []
         (gated w
                (when-let [e @ev]
                  (when (linked? w e)
                    (unlink! w e)
                    (commit! w [:unobserve (g e rw/ID)]))))))
      nil)))

(defn pin!
  "T20: a row is a root while its pin count is positive (Z#16)."
  [h]
  (admit-kind! h :pin)
  (let [m (calling-frame)]
    (try
      (gated (world-of h)
             (when-not (or (shut-roots! (cw) m)
                           (when-not (kind-ok? (row-of h) :pin)
                             (refuse! (cw) [:pin (g (row-of h) rw/ID)])
                             true))
               (let [x (row-of h) w (cw)
                     pins (g w rw/W-PINS)
                     n (long (or (second (hs/mget pins (id-of x))) 0))]
                 (hs/mput! pins (id-of x) [x (inc n)])
                 (ref-inc! x)
                 (commit! w [:pin (g x rw/ID)]))))
      (finally (leave-calling-frame! m))))
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
  "T19: `handles -= 1`; Rule R applies §3.4. The Cleaner can retain a
   pre-fork row, so resolve it under the receiving world's gate first."
  [w x]
  (let [x (rv w x)]
    (if (zero? (gl x rw/HANDLES))
      (refuse! w [:handle-drop (g x rw/ID)])
      (do (s! x rw/HANDLES (dec (gl x rw/HANDLES)))
          (when (zero? (gl x rw/REFS)) (aadd! (g w rw/W-RQ) x))
          (commit! w [:handle-drop (g x rw/ID)])))))

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

(defn fork-local?
  "Whether the task of handle `h` is fork-local (Z#77; `task-with`)."
  [h]
  (let [w (world-of h)] (host-call! w #(boolean (g (row-of h) rw/K-LOCAL)))))

(defn- holding-gate?
  "This thread is processing a world (a slice, a host item or a callback)."
  []
  (when-let [c (cw)] (hs/held? (g c rw/W-LOCK))))

(defn host-call!
  "R5: runs `(f)` as a host item of `w` and returns its value. Inside `w`
   (its slice, item or callback) it runs at once. Elsewhere the JVM caller
   waits outside the gate; a thread processing another world may not wait
   (B7: use send-world!). On CLJS the item is processed synchronously; a
   world that is not inline cannot answer synchronously."
  [w f]
  (cond
    (and (identical? w (cw)) (hs/held? (g w rw/W-LOCK))) (f)
    (holding-gate?)
    (throw (ex-info "host-call! while processing another world (B7): use send-world!"
                    {:spindel/invalid :host-call}))
    :else
    ;; the reply is tagged: on CLJS anything can be thrown, nil and false too
    #?(:clj (let [p (promise)]
              (host! w #(deliver p (try [::ok (f)] (catch Throwable t [::threw t]))))
              (let [[tag x] @p] (if (= ::threw tag) (throw x) x)))
       :cljs (let [box (volatile! ::none)]
               (host! w #(vreset! box (try [::ok (f)] (catch :default t [::threw t]))))
               (if (= ::none @box)
                 (throw (ex-info "host-call!: the world did not process the item synchronously" {}))
                 (let [[tag x] @box] (if (= ::threw tag) (throw x) x)))))))

(defn call-in!
  "Tooling and tests: host-call!."
  [w f]
  (host-call! w f))

(declare current-world)

(defn send-world!
  "R5: enqueues `(f)` as a host item of `w` and returns nil. Usable from a
   body or callback of another world: the item is only scheduled after the
   current gate is left, so no thread processes two worlds at once."
  [w f]
  (when (g w rw/W-RELEASED) (throw (released-ex)))
  (when (g w rw/W-SHUT) (throw (shut-ex w)))
  (hs/mpsc-add! (g w rw/W-INGRESS) f)
  (if (holding-gate?)
    (when-not (identical? w (cw)) (aadd! (g (cw) rw/W-AFTER) w))
    (handoff! w))
  nil)

;; ---------------------------------------------------------------------------
;; World state (M6 R1): application data of a world, outside the reactive
;; graph, forked by value. Engine references go in as world-neutral refs.

(defn handle? [x] (instance? Handle x))

(deftype Ref [^objects cell family])

(defn world-ref
  "A world-neutral row reference. Capsule ownership belongs to Handle
   objects and must never be copied into a Ref."
  [h]
  (try
    (let [cell (.-cell ^Handle h)
          row (aget ^objects cell 0)
          ref-cell (object-array [row])]
      (when-not row
        ;; The creating item may still be queued. Publish the pending ref
        ;; before rechecking row publication, closing bind-vs-ref races without
        ;; a global lock on ordinary handle construction/binding.
        (lt/locked #(do
                      (aset ^objects cell 2 (update (aget ^objects cell 2) :ref-cells (fnil conj []) ref-cell))
                      (when-let [row (aget ^objects cell 0)]
                        (aset ^objects ref-cell 0 row)
                        (aset ^objects cell 2 (update (aget ^objects cell 2) :ref-cells
                                                      (fn [refs] (vec (remove (fn [r] (identical? r ref-cell)) refs)))))))))
      (Ref. ref-cell (g (.-w ^Handle h) rw/W-FAMILY)))
    (finally (hs/fence! h))))

(defn ref? [x] (instance? Ref x))

(defn current-world
  "The world an operation acts on: the slice's world inside a body, else the
   bound *world*, else the world this thread is processing (a host item or a
   callback on a drainer thread)."
  []
  (if (and (active-run) (cw)) (cw) (or *world* (cw))))

(defn resolve-ref
  "The handle of `r`'s row in `w` (default: the current world). The row must
   be in `w`'s lineage (created by `w` or inherited from an ancestor before
   its fork), as for `in-world`: a row created in a child, or in a sibling
   after the fork, does not resolve elsewhere."
  ([r] (resolve-ref (current-world) r))
  ([w r]
   (when-not (identical? (g w rw/W-FAMILY) (.-family ^Ref r))
     (throw (ex-info "resolve-ref: the reference belongs to an unrelated world" {:spindel/invalid :lineage})))
   (let [x (aget ^objects (.-cell ^Ref r) 0)]
     ;; a ref to a row whose creation is still queued binds later (world-ref)
     (when (and x (not (inherited? w x))) (throw (lineage-ex x)))
     (new-handle w x))))

(defn- handle-swap!
  "swap! on a signal or cell handle: read and write in one host item. With
   `deltas?`, `f` sees the old value shallowly wrapped as a deltaable
   collection, and the operations it records become the write's deltas
   (§4.4); the stored value is always the plain one."
  ([h f] (handle-swap! h f (fn [_ n] n) true))
  ([h f ret deltas?]
   (let [w (world-of h)]
     (host-call! w #(let [x (row-of h)]
                      (when-not (and (source? x) (<= (gl x rw/X-KIND) rw/SRC-CELL))
                        (throw (invalid-op :swap "swap!/reset! is for signals and cells")))
                      (let [old (g x rw/X-VALUE)
                            n (f (if deltas? (dl/wrap-deltaable old) old))
                            [n ds] (if (and deltas? (dl/deltaable? n))
                                     [(dl/unwrap-deltaable n) (dl/get-deltas n)]
                                     [n nil])]
                        (write-d! h n ds)
                        (ret old n)))))))

(defn swap-changed?
  "swap! on a signal or cell, returning whether its value changed (old
   swap-signal-changed?)."
  [h f & args]
  (handle-swap! h #(apply f % args) (fn [old n] (not= old n)) true))

(defn- handle-row-id [h] (aget ^objects (aget ^objects (.-cell ^Handle h) 0) rw/ID))
(defn- handle-watch-token [h w]
  (let [cell (.-cell ^Handle h) row (aget ^objects cell 0)]
    (when-not (watchable-source? row)
      (throw (invalid-op :watch "watches are supported on signals and cells")))
    (if (identical? w (.-w ^Handle h))
      (aget ^objects cell 1)
      (let [owner (lt/locked
                   #(or (:foreign-owner (aget ^objects cell 2))
                        (let [o (lt/owner)]
                          (aset ^objects cell 2 (assoc (aget ^objects cell 2) :foreign-owner o)) o)))]
        (lt/owned-token! (g w rw/W-WATCHES) (g w rw/ID) (g row rw/ID) owner)))))

(defn- handle-watch-op! [h f]
  (try
    (let [w (world-of h)]
      (host-call! w #(f (handle-watch-token h w))))
    (finally (hs/fence! h))))

(defn- handle-watch! [h k f] (handle-watch-op! h #(lt/add-watch! % k f)))
(defn- handle-unwatch! [h k] (handle-watch-op! h #(lt/remove-watch! % k)))
(defn- handle-watches [h] (handle-watch-op! h #(deref (:callbacks %))))

(defn- handle-claim!
  "(d v) delivers a deferred (true when this call delivered it); (mb v)
   posts to a mailbox."
  [h v]
  (let [w (world-of h)]
    (host-call! w #(let [x (row-of h)]
                     (cond
                       (and (deferred? x) (not (link? x)))
                       (if (final? x) (do (deliver! h v) false) (do (deliver! h v) true))
                       (mailbox? x) (do (post! h v) nil)
                       :else (throw (invalid-op :invoke "only deferreds and mailboxes are invokable")))))))

(defn- check-state-value! [v]
  (when (instance? Handle v)
    (throw (ex-info "a handle in world state: store (world-ref h)" {:spindel/invalid :world-state}))))

(defn world-state
  "The world's application state (a persistent map)."
  [w]
  (host-call! w #(g w rw/W-STATE)))

(defn swap-world!
  "Atomically sets the world state to `(apply f state args)`; returns it. An
   effect at its site inside a body (not rolled back on re-run)."
  [w f & args]
  (host-call! w #(let [old (g w rw/W-STATE)
                       new (apply f old args)]
                   (s! w rw/W-STATE new)
                   (commit! w [:world-state (some-> (active-run) (g rw/ID)) [:opaque old] [:opaque new]])
                   new)))

(defn reset-world! [w m] (swap-world! w (constantly m)))
(defn get-in-world [w path] (get-in (world-state w) path))
(defn assoc-in-world! [w path v] (check-state-value! v) (swap-world! w assoc-in path v))
(defn update-in-world!
  [w path f & args]
  (swap-world! w (fn [m] (let [m (apply update-in m path f args)]
                           (check-state-value! (get-in m path))
                           m))))

;; ---------------------------------------------------------------------------
;; Atoms (M6 R6): clojure.core/atom semantics on a world's private atom
;; table, forked by value. The wrapper names an id, not a world: it acts on
;; the current world. Collected wrappers are dropped from the creating world
;; (forks keep their copy until they are dropped themselves).

(defn- missing-state [id]
  (ex-info "this world has no state for the atom" {:spindel/missing-state id}))

(defn- atom-world [family id]
  (let [w (or (current-world) (throw (ex-info "atom outside a world" {})))]
    (when-not (identical? family (g w rw/W-FAMILY)) (throw (missing-state id)))
    w))

(defn- atom-watch-op! [ref family id owner f]
  (try
    (let [w (atom-world family id)]
      (host-call! w #(if (contains? (g w rw/W-ATOMS) id)
                       (f (lt/owned-token! (g w rw/W-WATCHES) (g w rw/ID) id owner))
                       (throw (missing-state id)))))
    (finally (hs/fence! ref))))

(defn- atom-op!
  "Operate on the value, preserving the wrapper's weak entry. Fence on all
   paths, including failed user updates and throwing watch callbacks."
  [ref family id f]
  (try
    (let [w (atom-world family id)]
      (host-call! w #(let [m (g w rw/W-ATOMS)]
                       (if-let [[weak-ref old] (get m id)]
                         (let [[v' ret] (f old)]
                           (when-not (identical? v' old)
                             (s! w rw/W-ATOMS (assoc (g w rw/W-ATOMS) id [weak-ref v']))
                             (notify-watches! w id ref old v'))
                           ret)
                         (throw (missing-state id))))))
    (finally (hs/fence! ref))))

(deftype RAtom [^long id family ^:volatile-mutable mta watch-owner]
  #?@(:clj
      [clojure.lang.IDeref
       (deref [this] (atom-op! this family id (fn [v] [v v])))
       clojure.lang.IRef
       (addWatch [this k f] (atom-watch-op! this family id watch-owner #(lt/add-watch! % k f)) this)
       (removeWatch [this k] (atom-watch-op! this family id watch-owner #(lt/remove-watch! % k)) this)
       (getWatches [this] (atom-watch-op! this family id watch-owner #(deref (:callbacks %))))
       (getValidator [this] (hs/fence! this) nil)
       (setValidator [this _] (try (throw (ex-info "atoms take no validator" {:spindel/invalid :validator}))
                                   (finally (hs/fence! this))))
       clojure.lang.IMeta
       (meta [this] (try mta (finally (hs/fence! this))))
       clojure.lang.IReference
       (alterMeta [this f args] (try (set! mta (apply f mta args)) mta (finally (hs/fence! this))))
       (resetMeta [this m] (try (set! mta m) m (finally (hs/fence! this))))
       clojure.lang.IAtom
       (swap [this f] (atom-op! this family id (fn [v] (let [n (f v)] [n n]))))
       (swap [this f a] (atom-op! this family id (fn [v] (let [n (f v a)] [n n]))))
       (swap [this f a b] (atom-op! this family id (fn [v] (let [n (f v a b)] [n n]))))
       (swap [this f a b xs] (atom-op! this family id (fn [v] (let [n (apply f v a b xs)] [n n]))))
       (compareAndSet [this o n] (atom-op! this family id (fn [v] (if (identical? v o) [n true] [v false]))))
       (reset [this n] (atom-op! this family id (fn [_] [n n])))
       clojure.lang.IAtom2
       (swapVals [this f] (atom-op! this family id (fn [v] (let [n (f v)] [n [v n]]))))
       (swapVals [this f a] (atom-op! this family id (fn [v] (let [n (f v a)] [n [v n]]))))
       (swapVals [this f a b] (atom-op! this family id (fn [v] (let [n (f v a b)] [n [v n]]))))
       (swapVals [this f a b xs] (atom-op! this family id (fn [v] (let [n (apply f v a b xs)] [n [v n]]))))
       (resetVals [this n] (atom-op! this family id (fn [v] [n [v n]])))]
      :cljs
      [IDeref (-deref [this] (atom-op! this family id (fn [v] [v v])))
       IMeta (-meta [_] mta)
       IWatchable
       (-add-watch [this k f] (atom-watch-op! this family id watch-owner #(lt/add-watch! % k f)) this)
       (-remove-watch [this k] (atom-watch-op! this family id watch-owner #(lt/remove-watch! % k)) this)
       (-notify-watches [_ _ _] nil)
       IReset (-reset! [this n] (atom-op! this family id (fn [_] [n n])))
       ISwap
       (-swap! [this f] (atom-op! this family id (fn [v] (let [n (f v)] [n n]))))
       (-swap! [this f a] (atom-op! this family id (fn [v] (let [n (f v a)] [n n]))))
       (-swap! [this f a b] (atom-op! this family id (fn [v] (let [n (f v a b)] [n n]))))
       (-swap! [this f a b xs] (atom-op! this family id (fn [v] (let [n (apply f v a b xs)] [n n]))))]))

(defn atom
  "A fork-safe atom in the current world. Values are strong; a value that
   references its wrapper makes that wrapper application-reachable."
  [init & {:keys [meta]}]
  (let [w (or (current-world) (throw (ex-info "atom outside a world" {})))]
    (host-call! w #(let [id (alloc-id! w)
                         family (g w rw/W-FAMILY)
                         a (RAtom. id family meta (lt/owner))]
                     (s! w rw/W-ATOMS (assoc (g w rw/W-ATOMS) id [(hs/weak a) init]))
                     (lt/clean-atom-on-collection! a family request-atom-sweep!)
                     a))))

(defn value-async
  "T22/H3: demands `h` through a host wait edge and calls `(cb v err?)` once
   it settles. Returns a fn that withdraws the wait (host-unawait)."
  [h cb]
  (let [w (world-of h)
        ev (volatile! nil)]
    (gated w
           (let [d (row-of h)]
             (cond
               (g w rw/W-UNBORN)
               (aadd! (g w rw/W-CALLBACKS) [cb [(unborn-ex) true]])
               ;; T21: no new host wait after release, also from a cleanup slice
               (g w rw/W-RELEASED)
               (aadd! (g w rw/W-CALLBACKS) [cb [(released-ex) true]])
               (consuming? d)
               (aadd! (g w rw/W-CALLBACKS) [cb [(invalid-op :value "a host read of a mailbox or semaphore (Z#54)") true]])
               (stream? d)
               (aadd! (g w rw/W-CALLBACKS) [cb [(stream-ex) true]])
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
      (withdraw!
       (fn []
         (gated w
                (when-let [e @ev]
                  (when (linked? w e)
                    (unlink! w e)
                    (commit! w [:host-unawait (g e rw/ID)]))))))
      nil)))

(defn value
  "Host read (H3): blocks the calling host thread on a host promise, outside
   the gate. Never call it inside a body (B7). With a timeout, returns
   `timeout-val` when the result is not there in time."
  ([h] (value h nil nil))
  ([h timeout-ms timeout-val]
   (when (active-run) (throw (ex-info "blocking value inside a body (B7)" {})))
   ;; R7: a callback runs under the gate; waiting there would deadlock
   (when (holding-gate?) (throw (ex-info "blocking value while processing a world (B7)" {})))
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

(defn forked-ex [] (control-ex "forked" {:spindel/forked true}))

(declare join! cancel-resource! resource-fire! resource-ack! op-cancel!)

(defn- set-ctl!
  "A resource's physical controller, owned by world `w` (copies elsewhere
   drop it, F1)."
  [w z ctl]
  (s! z rw/Z-CTL ctl)
  (s! z rw/Z-ORIGIN (g w rw/ID)))

(defn- activate-dormant!
  "§8.1: a fork's inherited armed resources, at its first turn. A timer
   re-arms for its remaining time; any other resource (offload, external
   wait, savepoint: S3) never had a physical counterpart here: it fires err
   ::forked into its edges and joins at once. An instance's pending
   savepoint has fired by then (activate!)."
  [w]
  ;; C1 R1: inherited resources that were cancelling or fired but not yet
  ;; acknowledged have no counterpart here: they acknowledge now, without
  ;; touching the source's controller
  (when-let [zs (g w rw/W-DISCHARGE)]
    (s! w rw/W-DISCHARGE nil)
    (doseq [z0 zs]
      (let [z (rv w z0)]
        (when (not= rw/Z-ARMED (gl z rw/Z-PHASE))
          (resource-ack! w z)))))
  (when-let [zs (g w rw/W-DORMANT)]
    (s! w rw/W-DORMANT nil)
    (doseq [z0 zs]
      (let [z (rv w z0)]
        (when (== rw/Z-ARMED (gl z rw/Z-PHASE))
          (if (and (= :timer (g z rw/Z-KIND)) (g z rw/Z-DEADLINE))
            (let [left (max 0 (- (long (g z rw/Z-DEADLINE)) (hs/now-ms)))]
              (hs/oset-add! (armed-set w) (id-of z) z)
              (set-ctl! w z (hs/schedule! left (fn [] (join! w z [nil false])))))
            (do (resource-fire! w z [(forked-ex) true])
                (resource-ack! w z))))))))

(defn forked-local-ex
  "The error a waiter on a task retired in a fork receives (Z#77)."
  []
  (control-ex "forked" {:spindel/forked true :spindel/fork-local true}))

(defn- drop-entries!
  "Removes the elements `x` of list `l` with `(pred x)`."
  [l pred]
  (loop [i (dec (acount l))]
    (when-not (neg? i)
      (when (pred (anth l i)) (hs/remove-at! l i))
      (recur (dec i)))))

(defn- retire-local!
  "Z#77 T28 `[:retire-local]`, at a fork's first gate entry: the fork-local
   runs it inherited (W-RETIRE) are removed without running anything: no
   slice, finalizer, cleanup slice, host callback, resource fire or
   acknowledgement, timer re-arm. A task without a result fails with
   ::forked (fork-local), which its inherited waiters receive; the run
   scopes close with the sources they own (Z#18). Everything else stays."
  [w]
  (let [rs (into [] (comp (mapcat vals) (map #(rv w %))) (g w rw/W-RETIRE))
        ids (into #{} (map id-of) rs)
        mine? (fn [x] (contains? ids (id-of x)))
        zids (volatile! #{})]
    (s! w rw/W-RETIRE nil)
    ;; every run first, so that no retired run is filled or resumed below:
    ;; its activation goes (wait members unlinked), its resources with their
    ;; outstanding/dormant/discharge entries, its finalizers and slice
    (doseq [r rs]
      ;; a consuming wait (take!/acquire!) also leaves its source's FIFO
      (when-let [a (rv w (g r rw/R-ACTV))]
        (let [^objects ms (g a rw/A-MEMBERS)]
          (dotimes [i (alength ms)]
            (when-let [e (rv w (aget ms i))]
              (when (== rw/EK-WAIT (gl e rw/E-KIND))
                (let [d (rv w (g e rw/E-DEBTOR))]
                  (when (and (source? d) (<= rw/SRC-MAILBOX (gl d rw/X-KIND) rw/SRC-SEMAPHORE)
                             (g d rw/X-WAITERS))
                    (let [eid (id-of e)]
                      (hs/dq-remove-if! (deque d rw/X-WAITERS) #(== eid (id-of %)))))))))))
      (drop-activation! w r)
      (when-let [zs (g r rw/R-RES)]
        (dotimes [i (acount zs)]
          (let [z (rv w (anth zs i))]
            (vswap! zids conj (id-of z))
            (some-> (g w rw/W-OUTSTANDING) (hs/oset-del! (id-of z)))
            (some-> (g w rw/W-ARMED) (hs/oset-del! (id-of z)))
            (unregister! w z)))
        (s! r rw/R-RES nil))
      (s! r rw/R-ACT rw/ACT-DONE)
      (s! r rw/R-MODE 1)
      (s! r rw/R-SLICE false)
      (s! r rw/R-FINS 0))
    (let [zids @zids
          res? (fn [z] (contains? zids (id-of z)))]
      (when (seq zids)
        (s! w rw/W-DORMANT (seq (remove res? (g w rw/W-DORMANT))))
        (s! w rw/W-DISCHARGE (seq (remove res? (g w rw/W-DISCHARGE)))))
      (drop-entries! (g w rw/W-START) mine?)
      (drop-entries! (g w rw/W-RESUME) #(mine? (g % rw/A-RUN)))
      (drop-entries! (g w rw/W-CLEANUP) (fn [[x ek]] (if ek (mine? x) (res? x)))))
    ;; the debtor side (T10): a task without a result fails; inherited host
    ;; waits are the parent's and are not called (Z#45)
    ;; (one error per commit: the item's value, as the model's `retire-local v`)
    (let [ex (forked-local-ex)]
      (doseq [r rs] (finish-task! w (rv w (g r rw/R-OF)) ex true)))
    ;; T13: the runs retire, their scopes close with their sources (Z#18)
    ;; and go, and the tasks complete (C1c)
    (doseq [r rs] (retire! w r))
    (commit! w [:retire-local])
    (maybe-complete! w)))

(defn- new-resource!
  "T17: an outstanding resource owned by `r`, with `at = R.effect-index`."
  [w r kind at]
  (let [z (debtor-row w rw/T-RES rw/Z-SIZE r 0 at 0)]
    (s! z rw/Z-KIND kind)
    (s! z rw/Z-PHASE rw/Z-ARMED)
    (hs/oset-add! (armed-set w) (id-of z) z)
    (hs/oset-add! (or (g w rw/W-OUTSTANDING) (let [o (hs/oset)] (s! w rw/W-OUTSTANDING o) o))
                  (id-of z) z)                         ; C1 R1: until acknowledged
    (aadd! (or (gm r rw/R-RES) (let [l (alist)] (s! r rw/R-RES l) l)) z)
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
          zs (gm r rw/R-RES)
          i (idx-of zs z)]
      (when-not (neg? i)
        (hs/remove-at! zs i)
        (when (zero? (acount zs)) (s! r rw/R-RES nil))
        (some-> (g w rw/W-OUTSTANDING) (hs/oset-del! (id-of z)))
        (unregister! w z)
        ;; T15, then T13 within the item (Z#55)
        (retire-check! w r)
        (commit! w [:resource-ack (g z rw/ID)])))))

(defn- take-dormant! [w z]
  (when-let [zs (g w rw/W-DORMANT)]
    (let [id (id-of z)]
      (when (some #(== id (id-of %)) zs)
        (s! w rw/W-DORMANT (seq (remove #(== id (id-of %)) zs)))
        true))))

(defn- external-cancel!
  "R2: tells an external operation to cancel. True when it provably will not
   complete (its cancel fn answered :joined): the resource joins now."
  [{:keys [cancel flag ^objects cell]}]
  (if (hs/flag? flag)
    false                                   ; its completion is in flight and acks
    (let [r (when cancel (try (cancel) (catch #?(:clj Throwable :cljs :default) _ nil)))]
      (if (and (= :joined r) (hs/flag-cas! flag false true))
        (do (aset cell 0 nil) (aset cell 1 nil) true)
        false))))

(defn- cancel-resource!
  "T14: an armed resource is told to cancel. One that provably never started
   (or whose timer was unscheduled) joins at once; a running offload is
   interrupted and joins when its function returns. An await-op that
   delivered its result but has not finished is cancelled too (C1): its
   hooks run, and a detached one joins at once."
  [w z]
  (when (and (== rw/Z-FIRED (gl z rw/Z-PHASE)) (= :op (g z rw/Z-KIND)))
    (when-let [c (:op (g z rw/Z-CTL))]
      (when (op-cancel! c) (aadd! (g w rw/W-CLEANUP) [z]))))
  (when (== rw/Z-ARMED (gl z rw/Z-PHASE))
    (s! z rw/Z-PHASE rw/Z-CANCELLING)
    (hs/oset-del! (armed-set w) (id-of z))
    (let [ctl (g z rw/Z-CTL)
          ;; §8.1: an inherited resource still dormant here holds the source's
          ;; controller; it joins at once and never touches that controller
          joined? (or (take-dormant! w z)
                      (cond (nil? ctl) true
                            (hs/timer? ctl) (hs/unschedule! ctl)
                            (:external ctl) (external-cancel! ctl)
                            (:op ctl) (op-cancel! (:op ctl))
                            :else (hs/ctl-cancel! ctl)))]
      ;; the acknowledgement is its own item, after the cancelling one
      (when joined? (aadd! (g w rw/W-CLEANUP) [z])))))

(defn- arm-and-park!
  "T17 then T6 on the new resource, one effect and one commit (Z#55): the
   resource, its activation and the wait edge, in that id order."
  [r kind k ek start!]
  (let [w (cw)
        at (next-at! r)
        z (new-resource! w r kind at)
        aid (alloc-id! w)
        members (object-array 1)
        a (new-activation! w aid r :one k ek members (object-array 1) 1)
        e (link! w rw/EK-WAIT a z at)]
    (aset members 0 e)
    (park! r a)
    (s! a rw/A-INLINE false)
    (commit! w [:arm (g r rw/ID) kind [:opaque k] (g z rw/ID)])
    (notify-blocked! (rv w (g r rw/R-OF)) 0)
    (start! w z)
    nil))

(defn- join! [w z res]
  ;; the callback captured the row before any later fork: resolve it in `w`
  ;; a completion, not an admission: accepted after release (T21, L2)
  (internal! w #(let [z (rv w z)] (resource-fire! w z res) (resource-ack! w z))))

(defn offload-effect!
  "`(offload f)`: runs the plain function `f` on the world's executor,
   outside every world (§4.3). `f` must not call into the world
   synchronously; it may enqueue ingress."
  [f opts k ek]
  (if-let [refusal (finalizer-refusal)] (ek refusal)
          (if-let [r (valid-run)]
            (arm-and-park!
             r :offload k ek
             (fn [w z]
               (let [ctl (hs/offload-ctl)]
                 (set-ctl! w z ctl)
         ;; :pool runs f on another executor than the world's (M6 R8, blocking)
                 (hs/execute-or! (or (:pool opts) (g w rw/W-EXEC))
                      ;; a rejecting executor fails the effect (old blocking)
                                 (fn [t] (hs/ctl-cancel! ctl) (join! w z [t true]))
                                 (fn []
                                   (when (hs/ctl-start! ctl)
                                     (let [res (try [(f) false] (catch #?(:clj Throwable :cljs :default) t [t true]))]
                                       #?(:clj (do (hs/ctl-finish! ctl) (join! w z res))
                               ;; a returned promise is awaited (old blocking on JS)
                                          :cljs (if (and (not (second res)) (instance? js/Promise (first res)))
                                                  (.then (first res)
                                                         (fn [v] (hs/ctl-finish! ctl) (join! w z [v false]))
                                                         (fn [e] (hs/ctl-finish! ctl) (join! w z [e true])))
                                                  (do (hs/ctl-finish! ctl) (join! w z res)))))))))))
            (unwind! ek))))

(defn sleep-effect!
  "`(sleep ms)`: a timer resource."
  [ms k ek]
  (if-let [refusal (finalizer-refusal)] (ek refusal)
          (if-let [r (valid-run)]
            (arm-and-park!
             r :timer k ek
             (fn [w z]
               (s! z rw/Z-DEADLINE (+ (hs/now-ms) (long ms)))
               (set-ctl! w z (hs/schedule! ms (fn [] (join! w z [nil false]))))))
            (unwind! ek))))

(defn external-effect!
  "R2 `(external f)`: parks on an external operation. After the commit, under
   the gate, `(f complete!)` is called once; it must be finite and must not
   block, and returns nil or a cancel fn. `(complete! v)` / `(complete! e
   true)` may be called from any thread, once (later calls do nothing), and
   drops its references to the world once used. On cancel the cancel fn is
   called (also under the gate): `:joined` means the operation will not
   complete and the resource joins at once; anything else waits for the
   physical completion, whose value is dropped. If `f` throws, the effect
   fails with that error."
  [f k ek]
  (if-let [refusal (finalizer-refusal)] (ek refusal)
          (if-let [r (valid-run)]
            (arm-and-park!
             r :external k ek
             (fn [w z]
               (let [cell (doto (object-array 2) (aset 0 w) (aset 1 z))
                     flag (hs/flag false)
                     complete! (fn complete!
                                 ([v] (complete! v false))
                                 ([v err?]
                                  (when (hs/flag-cas! flag false true)
                                    (let [w (aget cell 0) z (aget cell 1)]
                                      (aset cell 0 nil) (aset cell 1 nil)
                                      (when w (join! w z [v (boolean err?)]))))
                                  nil))
                     ctl {:external true :flag flag :cell cell}]
                 (set-ctl! w z ctl)
                 (let [res (try [(f complete!) nil] (catch #?(:clj Throwable :cljs :default) t [nil t]))]
                   (if-let [t (second res)]
                     (complete! t true)
                     (when (fn? (first res))
                       (set-ctl! w z (assoc ctl :cancel (first res)))))))))
            (unwind! ek))))

;; ---------------------------------------------------------------------------
;; await-op (C1 W5/R3): a partial-cps op `(fn [resolve reject])` as a resource
;; with a controller. Start and cancel are arbitrated atomically; the result
;; (first resolve/reject) fires the resource; the resource acknowledges only
;; when start has returned, every committed cancel hook has returned, and the
;; op settled (or was cancelled before it started). `:detach` waives the
;; physical join. Start and hooks run on the world's executor after the gate.

(def ^:dynamic *op-ctl* nil)

;; controller: [0 state :new|:started|:never  1 cancelled?  2 result
;;              3 start-returned?  4 hooks  5 hooks-pending  6 acked?
;;              7 detach?  8 world  9 resource  10 executor]
(defn- op-ack-ready? [^objects c]
  (and (not (aget c 6))
       (zero? (long (aget c 5)))
       ;; cancelled before it started, or started, returned and settled (a
       ;; cancellation after start still waits for the physical result)
       (or (identical? :never (aget c 0))
           (and (aget c 3) (some? (aget c 2))))))

(defn- op-finish!
  "Acknowledges the resource once every part of the op is done."
  [^objects c]
  (let [wz (rw/locking-row c
                           (when (op-ack-ready? c)
                             (aset c 6 true)
                             (let [wz [(aget c 8) (aget c 9)]] (aset c 8 nil) (aset c 9 nil) wz)))]
    (when-let [[w z] wz]
      ;; the result's fire may still be queued: fire it here if not (the
      ;; fire item then finds the resource fired), so the ack never precedes it
      (when w (internal! w #(let [z (rv w z)
                                  res (rw/locking-row c (when-not (aget c 1) (aget c 2)))]
                              (when (and res (== rw/Z-ARMED (gl z rw/Z-PHASE))) (resource-fire! w z res))
                              (resource-ack! w z)))))))

(defn- op-run-hook! [^objects c f]
  (try (f) (catch #?(:clj Throwable :cljs :default) t
             #?(:clj (binding [*out* *err*] (println "await-op cancel hook failed:" t))
                :cljs (js/console.error "await-op cancel hook failed:" t))))
  (rw/locking-row c (aset c 5 (dec (long (aget c 5)))))
  (op-finish! c))

(defn- op-settle!
  "resolve/reject: the first result fires the resource (dropped after
   cancellation or detachment)."
  [^objects c v err?]
  (let [fire (rw/locking-row c
                             (when (nil? (aget c 2))
                               (aset c 2 [v (boolean err?)])
                               (when-not (aget c 1) [(aget c 8) (aget c 9)])))]
    (when-let [[w z] fire]
      (when w (internal! w #(let [z (rv w z)] (when (== rw/Z-ARMED (gl z rw/Z-PHASE)) (resource-fire! w z [v (boolean err?)]))))))
    (op-finish! c)))

(defn on-cancel!
  "Inside an `await-op` op's start: registers `f` to run once when the op is
   cancelled (at once if it already is). Hooks run on the executor, outside
   every world, and the op's join waits for them."
  [f]
  (let [^objects c (or *op-ctl* (throw (ex-info "on-cancel! outside an await-op start" {:spindel/invalid :on-cancel})))
        now? (rw/locking-row c
                             (if (aget c 1)
                               (do (aset c 5 (inc (long (aget c 5)))) true)
                               (do (aset c 4 (conj (aget c 4) f)) false)))]
    (when now? (op-run-hook! c f))
    nil))

(defn- op-cancel!
  "T14 on an :op resource, under the gate. True when it joins at once
   (cancelled before start, or detached)."
  [^objects c]
  (let [[hooks joined?]
        (rw/locking-row c
                        (if (aget c 1)
                          [nil false]
                          (do (aset c 1 true)
                              (let [before? (identical? :new (aget c 0))
                                    hooks (aget c 4)]
                                (when before? (aset c 0 :never))
                                (aset c 4 [])
                                (aset c 5 (+ (long (aget c 5)) (count hooks)))
                                (if (or before? (aget c 7))
                                  (do (aset c 6 true) (aset c 8 nil) (aset c 9 nil) [hooks true])
                                  [hooks false])))))]
    (when (seq hooks)
      (let [ex (aget c 10)]
        (aadd! (g (cw) rw/W-AFTER)
               #(doseq [f hooks] (hs/execute-or! ex (fn [_] (op-run-hook! c f)) (fn [] (op-run-hook! c f)))))))
    joined?))

(defn await-op-effect!
  "`(await-op op)` / `(await-op op {:detach true})`."
  [op opts k ek]
  (if-let [refusal (finalizer-refusal)] (ek refusal)
          (if-let [r (valid-run)]
            (let [#?@(:clj [frame (thread-frame)])]
              (arm-and-park!
               r :op k ek
               (fn [w z]
                 (let [ex (g w rw/W-EXEC)
                       c (object-array [:new false nil false [] 0 false (boolean (:detach opts)) w z ex])
                       start (fn []
                               (when (rw/locking-row c (when (identical? :new (aget c 0)) (aset c 0 :started) true))
                                 (try
                                   ;; B10: the run's bindings, plus the originating world
                                   #?(:clj (let [prev (clojure.lang.Var/getThreadBindingFrame)]
                                             (clojure.lang.Var/resetThreadBindingFrame frame)
                                             (try (push-thread-bindings {#'*op-ctl* c #'*world* w})
                                                  (try (op (fn [v] (op-settle! c v false)) (fn [e] (op-settle! c e true)))
                                                       (finally (pop-thread-bindings)))
                                                  (finally (clojure.lang.Var/resetThreadBindingFrame prev))))
                                      :cljs (binding [*op-ctl* c *world* w]
                                              (op (fn [v] (op-settle! c v false)) (fn [e] (op-settle! c e true)))))
                                   (catch #?(:clj Throwable :cljs :default) t (op-settle! c t true))
                                   (finally (rw/locking-row c (aset c 3 true)))))
                               (op-finish! c))]
                   (set-ctl! w z {:op c})
                   (aadd! (g w rw/W-AFTER)
                          #(hs/execute-or! ex
                                           ;; a rejecting executor fails the op
                                           (fn [t] (rw/locking-row c (aset c 0 :never)) (op-settle! c t true))
                                           start))))))
            (unwind! ek))))

;; ---------------------------------------------------------------------------
;; World completion (C1, c1-cancellation-joins-design.md W1-W2, R1-R2): a world
;; is complete when it is released, none of its runs is unretired and every
;; child world it owns is complete or was collected. Cancellation settles at
;; once (T14); completion is when the work has physically stopped.

(declare owned-done!)

(defn- kid-done!
  "Child token `t` ends once (the child completed, or was collected): its
   owner's obligation ends. Runs outside every gate (an after-gate action or
   a Cleaner). A counted child (C1c stage B) also ends its count: the owner
   runs [:owned-done s child], before which it cannot complete."
  [^objects t]
  (when (hs/flag-cas! (aget t 1) false true)
    (when-let [o (hs/deref-weak (aget t 0))]
      (when-let [sid (aget t 2)]
        (let [cid (aget t 3)] (internal! o #(owned-done! o sid cid))))
      (let [k (g o rw/W-KIDS)]
        (when (and (zero? (hs/kids-add! k -1)) (hs/kids-released? k))
          (internal! o #(maybe-complete! o)))))))

(defn- complete-world!
  "Marks `w` complete: its subscribers run and its owner is acknowledged,
   both after the gate."
  [w]
  (when-not (g w rw/W-COMPLETE)
    (s! w rw/W-COMPLETE true)
    ;; the owner first: a subscriber may wait for the owner's completion
    (when-let [kc (g w rw/W-KID-TOKEN)]
      (when-let [t (hs/kid-finish! kc)]
        (aadd! (g w rw/W-AFTER) #(kid-done! t))))
    (when-let [subs (g w rw/W-COMPLETE-SUBS)]
      (s! w rw/W-COMPLETE-SUBS nil)
      (dotimes [i (acount subs)]
        (let [[live cb] (anth subs i)]
          (when (hs/flag? live) (aadd! (g w rw/W-AFTER) #(when (hs/flag-cas! live true false) (cb)))))))
    ;; C1c: host joins still pending name tasks that never run again (an
    ;; unborn instance's copies): abandoned, delivered with the world
    (when-let [m (g w rw/W-JOIN-SUBS)]
      (s! w rw/W-JOIN-SUBS nil)
      (doseq [subs (vals m)] (deliver-subs! w subs)))))

(defn- maybe-complete!
  "W1: complete once released, with no unretired run and no owned child
   left; C1c stage B: no counted fork and nothing inherited to normalize."
  [w]
  (when (and (g w rw/W-RELEASED) (not (g w rw/W-COMPLETE))
             (zero? (gl w rw/W-RUNS))
             (let [k (g w rw/W-KIDS)] (or (nil? k) (zero? (hs/kids-count k))))
             (nil? (g w rw/W-OWNED-N))
             (nil? (g w rw/W-NORMALIZE)))
    (complete-world! w)))

(defn- owned-done!
  "C1c stage B: the counted child `cid` of scope `sid` completed or was
   collected: the count drops, and the scope goes if nothing else keeps it
   (Z#18). An internal item, accepted after release."
  [w sid cid]
  (let [m (g w rw/W-OWNED-N)]
    (when-let [[s n] (get m sid)]
      (s! w rw/W-OWNED-N (if (== 1 (long n)) (not-empty (dissoc m sid)) (assoc m sid [s (dec (long n))])))
      (when (== 1 (long n)) (when-let [s (rv w s)] (remove-scope-if-empty! w s)))
      (commit! w [:owned-done sid cid])
      (maybe-complete! w))))

(defn- normalize!
  "C1c stage B: a fork's first turn (an instance's activation) drains the
   counts it inherited: each owner scope goes if nothing else keeps it (Z#18)."
  [w]
  (when-let [m (g w rw/W-NORMALIZE)]
    (s! w rw/W-NORMALIZE nil)
    (doseq [s (vals m)] (when-let [s (rv w s)] (remove-scope-if-empty! w s)))
    (commit! w [:normalize])
    (maybe-complete! w)))

(defn- kid-collected!
  "C1 R2: a fork or instance was collected (its world's single collection
   action): if its owner accepted it and it never completed, the obligation
   ends (abandoned, F2). Runs outside every gate."
  [kc]
  (when-let [t (hs/kid-finish! kc)] (kid-done! t)))

(defn- kid-collector
  "The collection action's owner acknowledgement for a world's kid cell,
   built in its own function: a JS closure shares its enclosing function's
   context, so one made in fork-world* would also hold the child world and
   keep it alive (the FinalizationRegistry holds the action strongly)."
  [kc]
  (fn [] (kid-collected! kc)))

(defn- accept-child!
  "R2: owner `w` takes an obligation for `child` until its completion or its
   collection. A complete owner takes none. A child that is already done
   (completed or collected) acknowledges at once. `sid`: the scope it is
   counted on (C1c stage B), or nil."
  [w child sid]
  (when-not (g w rw/W-COMPLETE)
    (let [t (object-array [(hs/weak w) (hs/flag false) sid (g child rw/ID)])
          k (or (g w rw/W-KIDS)
                (let [k (hs/kids)] (when (g w rw/W-RELEASED) (hs/kids-released! k)) (s! w rw/W-KIDS k) k))]
      (hs/kids-add! k 1)
      (when-not (hs/kid-accept! (g child rw/W-KID-TOKEN) t)
        (kid-done! t)))))

(defn- internal-after!
  "`(f)` as an internal item of `w`, never taking two gates: from inside
   another world's gate it is scheduled after that gate is left."
  [w f]
  (if (and (holding-gate?) (not (identical? w (cw))))
    (do (hs/mpsc-add! (g w rw/W-INGRESS) f)
        (aadd! (g (cw) rw/W-AFTER) w))
    (internal! w f)))

(defn on-complete
  "W2: calls `(cb)` once, after the gate, when world `w` is complete
   (released, all its runs retired, its owned worlds complete); at once if
   it is. Accepted after release. Returns a fn that withdraws it."
  [w cb]
  (let [live (hs/flag true)]
    (internal-after! w (fn []
                         (if (g w rw/W-COMPLETE)
                           (aadd! (g w rw/W-AFTER) #(when (hs/flag-cas! live true false) (cb)))
                           (let [subs (or (g w rw/W-COMPLETE-SUBS) (let [l (alist)] (s! w rw/W-COMPLETE-SUBS l) l))]
                             ;; withdrawn entries are pruned as the list grows
                             (when (and (>= (acount subs) 16) (zero? (mod (acount subs) 16)))
                               (s! w rw/W-COMPLETE-SUBS
                                   (let [l (alist)]
                                     (dotimes [i (acount subs)]
                                       (when (hs/flag? (first (anth subs i))) (aadd! l (anth subs i))))
                                     l)))
                             (aadd! (g w rw/W-COMPLETE-SUBS) [live cb])))))
    (fn [] (hs/flag-set! live false) nil)))

(defn idle?
  "W6: a snapshot of world `w`: nothing runnable, no cleanup queued, no
   outstanding resource in any phase, nothing dormant and no queued ingress.
   Parked runs may remain (waiting on deferreds, positions, ...): idle is not
   complete. To wait for work to stop, release and use `on-complete`."
  [w]
  (host-call! w #(and (not (work-pending? w))
                      (let [o (g w rw/W-OUTSTANDING)] (or (nil? o) (zero? (hs/oset-count o))))
                      (nil? (g w rw/W-DORMANT))
                      (nil? (g w rw/W-DISCHARGE)))))

(defn complete?
  "Whether world `w` is complete (W1): a snapshot."
  [w]
  (boolean (g w rw/W-COMPLETE)))

#?(:clj
   (defn await-complete
     "JVM host: blocks until world `w` is complete; with a timeout, returns
      `timeout-val` if it is not in time (and withdraws). Returns true."
     ([w] (await-complete w nil nil))
     ([w timeout-ms timeout-val]
      (when (active-run) (throw (ex-info "blocking await-complete inside a body (B7)" {})))
      (when (holding-gate?) (throw (ex-info "blocking await-complete while processing a world (B7)" {})))
      (let [p (promise)
            withdraw (on-complete w #(deliver p true))]
        (if timeout-ms
          (let [r (deref p timeout-ms ::timeout)]
            (if (= ::timeout r) (do (withdraw) timeout-val) true))
          @p)))))

(defn on-joined
  "C1c: calls `(cb)` once, after the gate, when task `h` is complete: done,
   its run retired, and everything its run scope owned gone (its child tasks
   and explicit scopes; not computations, nor forks it owns: stage B). At
   once if it is, or if its world is complete (a task that never runs again,
   as in an unborn instance, is abandoned with its world). Makes no row, edge
   or handle; accepted after release. Returns a fn that withdraws it."
  [h cb]
  (let [x (when (instance? Handle h) (aget ^objects (.-cell ^Handle h) 0))]
    (when-not (and (instance? Handle h) (or (nil? x) (task? x)))   ; nil: not yet bound (H1)
      (throw (ex-info "on-joined: not a task handle" {:spindel/invalid :join}))))
  (let [w (world-of h)
        live (hs/flag true)]
    (internal-after! w (fn []
                         (let [k (row-of h)]
                           (cond
                             (not (and k (task? k))) nil   ; an unbound handle that named no task
                             (or (g k rw/K-COMPLETE) (g w rw/W-COMPLETE))
                             (deliver-subs! w [[live cb]])
                             :else
                             (let [m (or (g w rw/W-JOIN-SUBS) {})
                                   id (g k rw/ID)
                                   subs (get m id [])
                                   ;; withdrawn entries are pruned as the list grows
                                   subs (if (and (>= (count subs) 16) (zero? (mod (count subs) 16)))
                                          (filterv (comp hs/flag? first) subs)
                                          subs)]
                               (s! w rw/W-JOIN-SUBS (assoc m id (conj subs [live cb]))))))))
    (fn [] (hs/flag-set! live false) nil)))

#?(:clj
   (defn await-joined
     "JVM host: blocks until task `h` is complete (`on-joined`); with a
      timeout, returns `timeout-val` if it is not in time (and withdraws).
      Returns true."
     ([h] (await-joined h nil nil))
     ([h timeout-ms timeout-val]
      (when (active-run) (throw (ex-info "blocking await-joined inside a body (B7)" {})))
      (when (holding-gate?) (throw (ex-info "blocking await-joined while processing a world (B7)" {})))
      (let [p (promise)
            withdraw (on-joined h #(deliver p true))]
        (if timeout-ms
          (let [r (deref p timeout-ms ::timeout)]
            (if (= ::timeout r) (do (withdraw) timeout-val) true))
          @p)))))

(defn release-world!
  "T21: revokes the roots (observe callbacks and host waits receive
   ::released, pins are dropped), closes the root scope, and lets Rule R
   reclaim the rest. Later host operations fail with ::released. Returns a
   fn reporting the rows left (cleanup entries until they retire, L2)."
  [w]
  ;; idempotent: releasing a released world does nothing (old discard). Not
  ;; an admission: a release racing another one finds it done under the gate
  (when-not (g w rw/W-RELEASED)
    (internal! w (fn [] (release-world* w))))
  ;; the root scope is the administrative allowance (I11a): not a row left
  (fn [] (when-let [reg (g w rw/W-REG)] (dec (hs/msize reg)))))

(defn discard!
  "F4: releases a fork (T21 in it); its owner's marker goes (F2)."
  [w]
  (release-world! w))

(defn- release-world*
  "T21 inside `w`'s gate. Also the owner-close release of a fork (F2)."
  [w]
  (when-not (g w rw/W-RELEASED)
    (when-let [^objects h (g w rw/W-HOLDER)]
      (aset h 0 nil)
      (hs/flag-set! (aget h 2) true))
    (if (g w rw/W-UNBORN)
      ;; E4: an instance that never ran is discarded as if dropped: nothing
      ;; in it runs, its copied finalizers included
      (let [item (do (rule-r! w) (when (some? (g w rw/W-LOG)) (log-accept! w [:release-world])))]
          ;; the observer runs once the transition is complete (released)
        (s! w rw/W-RELEASED true)
        (observe-commit! w item)
        (finish-metadata! w) (maybe-finish-token! w)
          ;; nothing in it ever ran: complete at once (C1 W1, E4 abandonment)
        (some-> (g w rw/W-KIDS) hs/kids-released!)
        (complete-world! w))
      (let [ex (released-ex)
            roots (g w rw/W-ROOTS)]
        (doseq [e (map #(rv w %) (hs/mvals roots))]
          (when (linked? w e)
            (let [cb (rv w (g e rw/E-CRED))]
              (unlink! w e)
              ;; Z#45: an inherited root's callback is the parent's host's
              (when (= (g e rw/E-ORIGIN) (g w rw/ID))
                (aadd! (g w rw/W-CALLBACKS) [cb [ex true]])))))
        (let [pins (g w rw/W-PINS)]
          (doseq [[x n] (hs/mvals pins)] (dotimes [_ n] (ref-dec! w (rv w x))))
          (hs/mclear! pins))
        (close-scope! w (rv w (g w rw/W-ROOT)))
      ;; host admissions are revoked: released handles hold no row (T21)
        (when-let [reg (g w rw/W-REG)]
          (doseq [x0 (vec (hs/mvals reg))]
            (when (and (#{rw/T-COMP rw/T-TASK rw/T-SOURCE} (gl x0 rw/TYPE)) (pos? (gl x0 rw/HANDLES)))
              ;; a fork's own copy: an inherited basis row is shared with its parent
              (let [x (rv w x0)]
                (s! x rw/HANDLES 0)
                (when (zero? (gl x rw/REFS)) (aadd! (g w rw/W-RQ) x))))))
        (let [item (do (rule-r! w) (when (some? (g w rw/W-LOG)) (log-accept! w [:release-world])))]
          ;; the observer runs once the transition is complete (released)
          (s! w rw/W-RELEASED true)
          (some-> (g w rw/W-KIDS) hs/kids-released!)
          (observe-commit! w item))
        (maybe-complete! w)))))

(declare work-pending?)

(defn- maybe-finish-token!
  "MVCC: a released world whose cleanup has completed (metadata closed) and
   that has no work, queued cleanup or armed resource left ends its token
   (unless shared): nothing in it can read an inherited row any more."
  [w]
  (when (and (g w rw/W-RELEASED) (g w rw/W-META-CLOSED)
             (not (work-pending? w))
             (let [a (g w rw/W-ARMED)] (or (nil? a) (zero? (hs/oset-count a)))))
    (finish-token! w)))

(defn- finish-metadata! [w]
  (when (and (g w rw/W-RELEASED) (not (g w rw/W-META-CLOSED))
             (or (g w rw/W-UNBORN)
                 (let [root (rv w (g w rw/W-ROOT))]
                   (and (zero? (hs/oset-count (g root rw/S-TASKS)))
                        (zero? (acount (g root rw/S-CHILDREN)))))))
    (s! w rw/W-META-CLOSED true)
    (s! w rw/W-ATOMS {})
    (lt/clear-index! (g w rw/W-WATCHES) (g w rw/ID))
    (lt/unregister-world! (g w rw/W-FAMILY) (g w rw/ID))))

(defn open-scope!
  "T16 open: an explicit scope, child of the run's current scope, a root
   while open (§3.1). Used by `with-scope`."
  []
  (let [r (or (active-run) (throw (ex-info "with-scope outside a body" {})))
        w (cw)
        p (current-scope! w r)
        s (new-scope w (alloc-id! w) :explicit p)]
    (when (g p rw/S-LOCAL) (s! s rw/S-LOCAL true))   ; Z#77
    (aadd! (or (gm r rw/R-SCOPES) (let [l (alist)] (s! r rw/R-SCOPES l) l)) s)
    (commit! w [:open-scope (g r rw/ID) (g s rw/ID)])
    s))

(defn close-scope-fx!
  "T16 close at the end of `with-scope`: cancels the work it still owns."
  [s]
  (let [w (cw)
        s (rv w s)]                          ; captured before a fork: this world's copy
    (when-let [r (active-run)]
      (when-let [ss (gm r rw/R-SCOPES)]
        (let [i (last-idx-of ss s)]
          (when-not (neg? i) (hs/remove-at! ss i)))))
    (close-scope! w s)
    (commit! w [:close-scope (g s rw/ID)])
    nil))

(defn- within?
  "Whether scope `s` is `a` or below it: `a` is on `s`'s parent chain."
  [w s a]
  (loop [x s]
    (cond (nil? x) false
          (identical? x a) true
          :else (recur (rv w (g x rw/S-PARENT))))))

(defn detach!
  "Q10: re-owns a running task to an outer scope `s` (an explicit scope, or
   the world's root with `(root-scope w)`), so it outlives its creator. A
   scope in the task's own run-scope subtree is refused: the scope tree
   stays acyclic (Z#69)."
  [h s]
  (let [w (world-of h)]
    (gated w
           (let [k (row-of h)
                 family? (identical? (g s rw/S-WORLD) (g w rw/W-FAMILY))
                 s (if family? (rv w s) s)   ; e.g. (root-scope w): a raw row pointer
                 old (rv w (g k rw/OWNER))
                 rs (when-let [kr (rv w (g k rw/K-RUN))] (rv w (g kr rw/R-SROW)))]
             (if (or (g k rw/K-DONE) (not (g s rw/S-OPEN))
                     (not (and old (not (fn? old)) (== rw/T-SCOPE (gl old rw/TYPE))))
                     (not (and family? (inherited? w s)))   ; C1c: a scope of this world
                     (and rs (within? w s rs))
                     ;; Z#77: no unmarked task inside a fork-local subtree (LOC1)
                     (and (g s rw/S-LOCAL) (not (g k rw/K-LOCAL))))
               (refuse! w [:detach (g k rw/ID) (g s rw/ID)])
               (do
                 (hs/oset-del! (gm old rw/S-TASKS) (id-of k))
                 (hs/oset-add! (gm s rw/S-TASKS) (id-of k) k)
            ;; the run scope's parent follows the owner (Z#26)
                 (when rs
                   (remove-row! (gm old rw/S-CHILDREN) rs)
                   (s! rs rw/S-PARENT s)
                   (aadd! (gm s rw/S-CHILDREN) rs))
                 (s! k rw/OWNER s)
                 (remove-scope-if-empty! w old)
                 (commit! w [:detach (g k rw/ID) (g s rw/ID)])))))
    h))

(defn root-scope [w] (g w rw/W-ROOT))

(defn in-world
  "A handle naming the same row as `h`, in world `w` (e.g. a fork). The row
   resolves to `w`'s copy when `w` processes it."
  [w h]
  (when-not (identical? (g w rw/W-FAMILY) (g (.-w ^Handle h) rw/W-FAMILY))
    (throw (ex-info "in-world: the handle belongs to an unrelated world" {:spindel/invalid :lineage})))
  (let [x (aget ^objects (.-cell ^Handle h) 0)]
    (when-not (inherited? w x) (throw (lineage-ex x)))
    (new-handle w x)))

(defn- publish-world!
  "Registers the constructed world `c` with its family. The registry
   insertion publishes it: from then on the family's atom maintenance can
   enter `c` and hand it off (a stale copied sweep generation, or a
   concurrent atom collection, schedules that at once), so every field a
   first entry reads must be set before. `fork-world*` and `instance-world*`
   leave this to their callers. The collection action is installed before
   the insertion. With `failed!` (non-throwing), a throw after the insertion
   goes to `(failed! t)`: it is a failure of a published world; only a throw
   before the insertion propagates."
  ([c] (publish-world! c nil))
  ([c failed!]
   (lt/register-world! (g c rw/W-FAMILY) c (g c rw/ID) (g c rw/W-WATCHES)
                       (gl c rw/W-SWEEP-GEN) request-atom-sweep!
                       (kid-collector (g c rw/W-KID-TOKEN)) failed!)))

(defn- fork-world*
  "D3: the copy-on-write fork of `w` at the current commit (MVCC, §2.7). O(1)
   in the world's rows: `w` keeps owning them and advances its ordinal, so it
   saves a row's state as a version before its first change (for this fork,
   while its token lives); the child reads `w`'s rows at the fork's ordinal
   through its lineage and copies what it touches. The child gets fresh
   administration and copies of the queues, pins and roots (work in flight,
   design v3 §6); its inherited armed resources are dormant until its first
   turn (§8.1). The child is not yet published to its family
   (`publish-world!`). With `init` (child id -> world state), the child's
   world state is `(init id)`, evaluated right after the child's id is
   allocated and before anything else changes: its throw leaves only that
   id unused."
  ([w] (fork-world* w nil))
  ([w init]
   (let [id (alloc-id! w)
         st (when init (init id))
         c (aclone ^objects w)
         armed (g w rw/W-ARMED)
         o (rw/epoch-ordinal (g w rw/W-EPOCH))
         _ (share-token! w)
         tok (register-token! w o)]
     (when init (s! c rw/W-STATE st))
     (s! w rw/W-EPOCH (rw/epoch (g w rw/ID) (inc o)))
     (s! c rw/ID id)
     (s! c rw/W-EPOCH (rw/epoch id 0))
    ;; lineage: w's rows below the child's id are its basis (§8.1), read at
    ;; ordinal o (the token keeps those versions); w's copy map as it is now
     (s! c rw/W-LINEAGE (cons [(g w rw/ID) id o tok (g w rw/W-FWD)] (g w rw/W-LINEAGE)))
     (s! c rw/W-FWD {})
     (s! c rw/W-TOKENS nil)
     (s! c rw/W-LOCK (hs/lock))
     (s! c rw/W-INGRESS (hs/mpsc))
     (s! c rw/W-SCHEDULED (hs/flag false))
     (s! c rw/W-DRAINING false)
     (s! c rw/W-CALLBACKS (alist))
    ;; lifecycle state is the world's own, never inherited (spec §8.1 D3)
     (s! c rw/W-OWNED nil)
    ;; C1c stage B: the parent's counts are the child's to normalize, with
    ;; what the parent itself has not normalized yet
     (s! c rw/W-OWNED-N nil)
     (s! c rw/W-NORMALIZE (not-empty (reduce-kv (fn [m sid [s _]] (assoc m sid s))
                                                (or (g w rw/W-NORMALIZE) {}) (g w rw/W-OWNED-N))))
     (s! c rw/W-HOLDER nil)
     (s! c rw/W-AFTER (alist))
     (s! c rw/W-UNBORN false)
     (s! c rw/W-SHUT nil)
     (s! c rw/W-PUB-WORLD nil)
     (s! c rw/W-WATCHES (lt/index))
     (s! c rw/W-SWEEP-PENDING (hs/flag false))
     (s! c rw/W-META-CLOSED false)
    ;; Z#77: the fork-local runs are retired at the child's first gate entry
    ;; (T28), with what this world has not retired itself (a basis)
     (s! c rw/W-LOCAL nil)
     (s! c rw/W-RETIRE (let [l (g w rw/W-LOCAL)] (if l (cons l (g w rw/W-RETIRE)) (g w rw/W-RETIRE))))
     (doseq [i [rw/W-READY rw/W-RESUME rw/W-START rw/W-CLEANUP rw/W-RQ]]
       (s! c i (hs/lcopy (g w i))))
     (s! c rw/W-PINS (hs/mcopy (g w rw/W-PINS)))
     (s! c rw/W-ROOTS (hs/mcopy (g w rw/W-ROOTS)))
     (s! c rw/W-ARMED nil)
    ;; dormant: this world's armed resources (savepoints among them), plus
    ;; what it still holds dormant itself (a basis is never run, only forked)
     (s! c rw/W-DORMANT (seq (concat (when armed (hs/oset-vals armed)) (g w rw/W-DORMANT))))
    ;; C1: the child inherits every unretired run (W-RUNS, copied) and every
    ;; outstanding resource; the non-armed ones are discharged at its first
    ;; turn (R1); its own completion ledger starts empty (W1, R2)
     (let [o (g w rw/W-OUTSTANDING)
           o (when (and o (pos? (hs/oset-count o))) o)]
       (s! c rw/W-OUTSTANDING (when o (hs/oset-copy o)))
       (s! c rw/W-DISCHARGE (seq (concat (when o (remove #(and armed (some? (hs/oset-get armed (id-of %))))
                                                         (hs/oset-vals o)))
                                         (g w rw/W-DISCHARGE)))))
     (s! c rw/W-KIDS nil)
     (s! c rw/W-KID-TOKEN (hs/kid-cell))
     (s! c rw/W-COMPLETE false)
     (s! c rw/W-COMPLETE-SUBS nil)
     (s! c rw/W-JOIN-SUBS nil)
     (s! c rw/W-PENDING-ACT nil)
     (s! c rw/W-MBASE nil)
     (s! c rw/W-SEALED (hs/flag false))   ; C2: a fork starts unsealed
     (s! c rw/W-ADMITTING (hs/kids))
     (s! c rw/W-MPARENT nil)
     (when-let [reg (g w rw/W-REG)]
      ;; verify mode: the child's registry holds the rows as they are at the
      ;; fork (the parent keeps changing its own in place)
       (s! c rw/W-REG (let [m (hs/mcopy reg)]
                        #?(:clj (doseq [^java.util.Map$Entry e (vec (.entrySet ^java.util.Map m))]
                                  (.put ^java.util.Map m (.getKey e) (image (.getValue e))))
                           :cljs (doseq [[k v] (vec (es6-iterator-seq (.entries m)))]
                                   (.set m k (image v))))
                        m))
       (s! c rw/W-LOG (alist)))
     c)))

(defn- instance-world*
  "S3: a fork of the savepoint basis `b` (never run, owns no rows): the basis
   is not changed (no ordinal, no token); the instance reads through the
   basis's lineage, whose tokens keep the versions it needs. Born with all
   its birth fields (E4: unborn, its pending activation `act`, its owner, its
   initial world state), not yet published to its family (`publish-world!`)."
  [b act owner state]
  (share-token! b)
  (let [c (aclone ^objects b)
        id (alloc-id! b)]
    (s! c rw/ID id)
    (s! c rw/W-EPOCH (rw/epoch id 0))
    (s! c rw/W-FWD {})
    (s! c rw/W-TOKENS nil)
    (s! c rw/W-LOCK (hs/lock))
    (s! c rw/W-INGRESS (hs/mpsc))
    (s! c rw/W-SCHEDULED (hs/flag false))
    (s! c rw/W-DRAINING false)
    (s! c rw/W-CALLBACKS (alist))
    (s! c rw/W-OWNED nil)
    (s! c rw/W-OWNED-N nil)             ; a basis never runs: it has no counts, only W-NORMALIZE
    (s! c rw/W-HOLDER nil)
    (s! c rw/W-AFTER (alist))
    ;; E4: unborn until activate!: host items commit, but its inherited work
    ;; and dormant resources wait; dropped unactivated, it is collected
    ;; without running anything (it never ran)
    (s! c rw/W-UNBORN true)
    (s! c rw/W-SHUT nil)                ; a basis is frozen, its instances are not
    (s! c rw/W-PUB-WORLD owner)
    (s! c rw/W-STATE state)
    (s! c rw/W-WATCHES (lt/index))
    (s! c rw/W-SWEEP-PENDING (hs/flag false))
    (s! c rw/W-META-CLOSED false)
    (doseq [i [rw/W-READY rw/W-RESUME rw/W-START rw/W-CLEANUP rw/W-RQ]]
      (s! c i (hs/lcopy (g b i))))
    (s! c rw/W-PINS (hs/mcopy (g b rw/W-PINS)))
    (s! c rw/W-ROOTS (hs/mcopy (g b rw/W-ROOTS)))
    (s! c rw/W-ARMED nil)
    (s! c rw/W-DORMANT (g b rw/W-DORMANT))
    (s! c rw/W-OUTSTANDING (some-> (g b rw/W-OUTSTANDING) hs/oset-copy))
    (s! c rw/W-DISCHARGE (g b rw/W-DISCHARGE))
    (s! c rw/W-KIDS nil)
    (s! c rw/W-KID-TOKEN (hs/kid-cell))
    (s! c rw/W-COMPLETE false)
    (s! c rw/W-COMPLETE-SUBS nil)
    (s! c rw/W-JOIN-SUBS nil)
    (s! c rw/W-PENDING-ACT act)
    (s! c rw/W-MBASE nil)
    (s! c rw/W-SEALED (hs/flag false))   ; C2: a fork starts unsealed
    (s! c rw/W-ADMITTING (hs/kids))
    (s! c rw/W-MPARENT nil)
    (when-let [reg (g b rw/W-REG)]
      (s! c rw/W-REG (hs/mcopy reg))
      (s! c rw/W-LOG (alist)))
    c))

(defn- host-fork-call!
  "host-call! of `f`, a host fork of `w`. A slice or callback of another
   world may not wait for `w` (B7): there `w` forks at once when it can take
   the item now (H2), else the fork is refused. An item `w`'s drainer took
   meanwhile is short and never waits, so its result is awaited."
  [w f]
  (if (and (holding-gate?) (not (identical? w (cw))))
    (let [claim (hs/flag false)
          res (volatile! nil)]
      (gated w (when (hs/flag-cas! claim false true)
                 (vreset! res (try [::ok (f)] (catch #?(:clj Throwable :cljs :default) t [::threw t])))))
      (if (hs/flag-cas! claim false true)
        (throw (ex-info "fork!: the world is busy, and a body of another world may not wait for it (B7)"
                        {:spindel/invalid :busy}))
        (let [[tag x] (loop [] (or @res (do #?(:clj (Thread/onSpinWait)) (recur))))]
          (if (= ::threw tag) (throw x) x))))
    (host-call! w f)))

(defn- fork-host-item!
  "D3, the host fork item of `w` with its default owner (`fork!`), under
   `w`'s gate. In order:
   1. refused (a throw, no log item, nothing allocated) when `w` is unborn
      or released: an item admitted before T21 can run after it, and a fork
      from inside a host item of `w` bypasses ingress admission (H1);
   2. the child's id is allocated, then `init-state` (pure,
      `(f state {:world-id id})`) is applied to `w`'s world state before
      anything else changes: its throw is the fork's, and leaves only an
      unused id (an allocator gap: no MVCC token, epoch step or log item);
   3. the child is built privately (`fork-world*`) with that world state and
      the merge fields; its verify fields are set by the copy;
   4. `w`'s root scope owns it, weakly (F2);
   5. acceptance: Rule R and the logged `[:fork-host c]` (`commit!`). The
      outcome is fixed here; the commit observer is isolated (`log-commit!`);
   6. publication: the child's collection action, then the family registry
      insertion. From then on the family's atom maintenance can enter the
      child (on its own thread, also before `w`'s gate is released); a
      failure after the insertion (the sweep request) is the published
      child's, reported, and the child stays published and owned. A failure
      before it leaves the child unpublished: its host admission is shut at
      once, it is released through its ingress (processed after `w`'s gate)
      and the fork throws
      `{:spindel/unpublished true :child c}`;
   7. `W-AFTER`: the child is handed off after `w`'s gate is released. This
      is the fork's only handoff of the child (`fork!` adds none).
   Returns the child."
  [w init-state mergeable?]
  (when (g w rw/W-UNBORN) (throw (ex-info "fork! of an unactivated instance" {})))
  (when (g w rw/W-RELEASED) (throw (released-ex)))
  (let [c (fork-world* w (when init-state
                           (fn [id] (init-state (g w rw/W-STATE) {:world-id id}))))]
    (when mergeable?
      (s! c rw/W-MPARENT (g w rw/ID))
      (s! c rw/W-MBASE {}))
    (own-child! w (rv w (g w rw/W-ROOT)) c false)   ; F2: weakly, by the root scope
    (commit! w [:fork-host (g c rw/ID)])
    (try (publish-world! c #(report! "fork publication" %))
         (catch #?(:clj Throwable :cljs :default) t
           ;; no host work is admitted to it after this decision
           (s! c rw/W-SHUT :released)
           (release-child! w c)
           (throw (ex-info "fork!: the accepted child could not be published to its family; it is released"
                           {:spindel/unpublished true :child c} t))))
    ;; the child's inherited work is scheduled after this gate, also when
    ;; the caller stopped waiting for the reply (D)
    (aadd! (g w rw/W-AFTER) c)
    c))

(defn fork!
  "D3, host form: a frozen fork of `w` between slices. Returns the child
   world; act on it through `in-world` handles. With `{:mergeable? true}`
   the child keeps the basis of every source it inherited and touches, so
   `merge!` can adopt its writes into `w`. With `{:init-state f}` the
   child's world state starts as `(f state {:world-id id})`: `state` is
   `w`'s at the fork, `id` the child's world id (`world-id`); `f` is pure.
   The child's first entry sees it. With `{:owner o}` (a world of
   the same family) the root scope of `o` owns the child instead of `w`'s
   (F2), so it outlives `w`, as an instance outlives its publication's world
   (S3); `:init-state` is not supported with another owner.

   With its default owner the fork commits before the child is published to
   its family, and the child is returned once committed (`fork-host-item!`);
   it is handed off after the gate that processed the fork is released,
   never under it. From inside a host item of `w` (H1) the fork runs in that
   item."
  ([w] (fork! w nil))
  ([w opts]
   ;; a body forks its own world with the (fork) effect; a host fork of
   ;; another world is a host operation of that world, also from a body
   (when (and (active-run) (identical? w (cw)))
     (throw (ex-info "fork! inside a body: use the (fork) effect" {})))
   (let [owner (:owner opts)
         init-state (:init-state opts)
         other-owner? (and owner (not (identical? owner w)))]
     (when (and owner (not (identical? (g owner rw/W-FAMILY) (g w rw/W-FAMILY))))
       (throw (ex-info "fork!: the owner belongs to an unrelated world" {:spindel/invalid :lineage})))
     (when (and other-owner? init-state)
       (throw (ex-info "fork!: :init-state with another :owner is not supported"
                       {:spindel/invalid :init-state})))
     (if-not other-owner?
       ;; the child is handed off from `w`'s W-AFTER only, after the gate
       ;; that processed the item is released: a queued caller's reply is
       ;; delivered from inside that gate
       (host-fork-call! w #(fork-host-item! w init-state (:mergeable? opts)))
       (let [c (host-fork-call!
                w
                (fn []
                  (when (g w rw/W-UNBORN) (throw (ex-info "fork! of an unactivated instance" {})))
                  (let [c (fork-world* w)]
                    (publish-world! c)
                    (when (:mergeable? opts)
                      (s! c rw/W-MPARENT (g w rw/ID))
                      (s! c rw/W-MBASE {}))
                    ;; as activate!: the owner's gate is only tried, never waited
                    ;; for (E3); a released owner releases the child
                    (try (host! owner #(own-child! owner (rv owner (g owner rw/W-ROOT)) c false))
                         (catch #?(:clj Exception :cljs :default) _
                           (release-child! w c)))
                    (commit! w [:fork-host (g c rw/ID)])
                    ;; the child's inherited work is scheduled after this gate,
                    ;; also when the caller stopped waiting for the reply (D)
                    (aadd! (g w rw/W-AFTER) c)
                    c)))]
         (handoff! c)
         c)))))

(defn- quiescent*
  "§9 under the gate: no unretired run, no cleanup entry, no outstanding
   resource, nothing queued (C2, model F2: a parked run's armed resource
   could fire and write after a seal)."
  [w]
  (and (zero? (hs/kids-count (g w rw/W-ADMITTING)))   ; checked first: then the queue
       (zero? (gl w rw/W-RUNS))
       (zero? (acount (g w rw/W-CLEANUP)))
       (let [o (g w rw/W-OUTSTANDING)] (or (nil? o) (zero? (hs/oset-count o))))
       (not (work-pending? w))))

(defn- refuse-merge [_ident _base _parent-value _child-value] ::refuse)

(defn- merge-entries
  "L12 under both gates: [[parent-row value] ...] for every inherited source
   `child` changed, or nil when the merge is refused: the child is not a
   sealed, quiescent (§9), born, live mergeable fork of `parent`; or a
   changed source is not an open signal the parent still holds; or the
   parent changed it since the fork and `resolve` refuses (C2): it gets
   the parent-resolved identity, the base value, the parent's and the
   child's value and returns the merged value or ::refuse. It runs under
   both gates: pure, no world operation (B7); a throw is a refusal."
  [parent child resolve]
  (when (and (g child rw/W-MBASE)
             (hs/flag? (g child rw/W-SEALED))
             (== (long (g parent rw/ID)) (long (g child rw/W-MPARENT)))
             (not (g child rw/W-RELEASED)) (not (g child rw/W-UNBORN)) (not (g child rw/W-DRAINING))
             (quiescent* child))
    (let [cfwd (g child rw/W-FWD)
          reg (g parent rw/W-REG)]
      (reduce-kv
       (fn [acc id [ident ^long base base-v]]
         (let [cx (get cfwd id)]
           (if (or (nil? cx) (== base (gl cx rw/VERSION)))
             acc
             ;; the parent's current state, without copying (it owns the row,
             ;; or reads it through its own lineage)
             (let [px (peek-row parent ident)]
               (if-not (and (== rw/SRC-SIGNAL (gl px rw/X-KIND)) (== rw/SRC-SIGNAL (gl cx rw/X-KIND))
                            (g px rw/X-OPEN)
                            (if reg (some? (hs/mget reg id)) (or (pos? (gl px rw/REFS)) (pos? (gl px rw/HANDLES)))))
                 (reduced nil)
                 (if (== base (gl px rw/VERSION))
                   (conj acc [ident (g cx rw/X-VALUE)])
                   (let [v (try (resolve ident base-v (g px rw/X-VALUE) (g cx rw/X-VALUE))
                                (catch #?(:clj Throwable :cljs :default) _ ::refuse))]
                     (if (= ::refuse v) (reduced nil) (conj acc [ident v])))))))))
       ;; in id order: the writes are items, and their order is part of the log
       [] (into (sorted-map) (g child rw/W-MBASE))))))

(defn merge!
  "L12/C2: adopts the writes of the mergeable fork `child` into its parent
   `parent`: every inherited signal the child changed is written in the
   parent (T2 each, one host item), then the child is released. The child
   must be sealed (`seal!`) and quiescent (§9: no unretired run, cleanup
   entry or outstanding resource). A source the parent also changed since
   the fork is a conflict: `(:resolve opts)`, called as
   `(f ident base parent-value child-value)`, returns the merged value or
   ::refuse (the default refuses every conflict). Refused, changing neither
   world, on any refusal, or when `parent` is itself sealed. Sources created
   in the child are not merged. True when merged. The caller waits for the
   item (as `host-call!`, B7: not from a thread processing another world),
   and the item waits out a turn or metadata job holding the child's gate:
   neither is a refusal."
  ([parent child] (merge! parent child nil))
  ([parent child opts]
   (let [resolve (or (:resolve opts) refuse-merge)]
     (host-call!
      parent
      (fn []
        (let [lk (g child rw/W-LOCK)]
          (if (or (active-run) (identical? parent child) (hs/held? lk) (hs/flag? (g parent rw/W-SEALED)))
            false
            ;; deadlock-free: a holder of the child's gate never waits for another
            ;; gate (B7), and metadata jobs only try
            (do (hs/lock! lk)
                (let [es (try (merge-entries parent child resolve)
                              (finally (hs/unlock! lk) (handoff! child)))]
                  (if-not es
                    false
                    (do (doseq [[basis v] es]
                          (let [x (rv parent basis)
                                ref (let [r (g x rw/HREF)] (if (instance? Handle r) r (some-> r hs/deref-weak)))]
                            (write-row! parent x ref v)))
                        (release-child! parent child)
                        true)))))))))))

(defn seal!
  "C2 (§9): `w` refuses host admissions (task and computation starts,
   observe) and host source changes (write, swap, deliver, post, release,
   append, close) until `unseal!`; its bodies and propagation continue.
   Idempotent. A sealed world's `diff` is stable once it is quiescent."
  [w]
  (host-call! w #(do (hs/flag-set! (g w rw/W-SEALED) true) nil)))

(defn unseal!
  "C2: lifts `seal!`. A diff or preflight read before is stale: reseal and
   reread. Refused (::released) in a released world, a merged one included."
  [w]
  (host-call! w #(do (when (g w rw/W-RELEASED) (throw (released-ex)))
                     (hs/flag-set! (g w rw/W-SEALED) false)
                     nil)))

(defn sealed? [w] (hs/flag? (g w rw/W-SEALED)))

(defn diff
  "C2 (§9): the inherited sources the mergeable fork `w` changed, as
   {source-handle {:base base-value :value value}} (in the parent's terms,
   a handle of `w`). Sources created in `w` are not listed. nil for a fork
   that is not mergeable."
  [w]
  (host-call! w (fn []
                  (when-let [mb (g w rw/W-MBASE)]
                    (let [fwd (g w rw/W-FWD)]
                      (reduce-kv (fn [acc id [ident ^long base base-v]]
                                   (let [cx (get fwd id)]
                                     (if (or (nil? cx) (== base (gl cx rw/VERSION)))
                                       acc
                                       (assoc acc (new-handle w ident) {:base base-v :value (g cx rw/X-VALUE)}))))
                                 {} (into (sorted-map) mb)))))))

(defn- owner-world
  "The world whose obligation `w` is (its accepted kid token's owner), or nil."
  [w]
  (when-let [kc (g w rw/W-KID-TOKEN)]   ; a root world is nobody's obligation
    (let [t (hs/kid-token kc)]
      (when-not (or (nil? t) (keyword? t)) (hs/deref-weak (aget ^objects t 0))))))

(defn- owned-below?
  "Whether `x` is `w` or a world `w` owns, directly or further down."
  [x w]
  (loop [x x n 0]
    (cond (nil? x) false
          (identical? x w) true
          (> n 10000) false
          :else (recur (owner-world x) (inc n)))))

(defn transfer!
  "C2 R6: `new-owner` (a world of the same family) takes over the ownership
   of the fork `child` from its current owner: the child's completion (or
   collection) acknowledges `new-owner`, and closing `new-owner` releases
   it; the old owner no longer waits for it (and may complete). Only a fork
   owned by a root scope (`fork!`, `:owner`, an instance) moves; the child of
   a body's `(fork)` stays in its scope (stage B). Refused, changing nothing
   (false): a child that is done, released or counted; `new-owner` that is
   the current owner, released or complete, or the child itself or a world
   the child owns (an ownership cycle). True when moved. Two steps, as the
   model's sys-xfer-reserve/-move: `new-owner` reserves the obligation, then
   the old owner hands the child over under the child's gate, or the
   reservation is undone. Host operation (B7: not from a world's turn)."
  [child new-owner]
  (when-not (identical? (g child rw/W-FAMILY) (g new-owner rw/W-FAMILY))
    (throw (ex-info "transfer!: the new owner belongs to an unrelated world" {:spindel/invalid :lineage})))
  (let [kc (g child rw/W-KID-TOKEN)
        t1 (some-> kc hs/kid-token)
        old (when-not (or (nil? t1) (keyword? t1)) (hs/deref-weak (aget ^objects t1 0)))]
    (if (or (nil? old) (identical? old new-owner) (some? (aget ^objects t1 2))
            (owned-below? new-owner child))
      false
      (let [t2 (try
                 (host-call! new-owner
                             (fn []
                               (when-not (or (g new-owner rw/W-RELEASED) (g new-owner rw/W-COMPLETE))
                                 (let [k (or (g new-owner rw/W-KIDS)
                                             (let [k (hs/kids)] (s! new-owner rw/W-KIDS k) k))]
                                   (hs/kids-add! k 1)
                                   (object-array [(hs/weak new-owner) (hs/flag false) nil (g child rw/ID)])))))
                 ;; a released new owner refuses the host item: no reservation
                 (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) e
                   (if (:spindel/released (ex-data e)) nil (throw e))))]
        (if-not t2
          false
          (let [moved (try
                        (host-call!
                         old
                         (fn []
                           (let [lk (g child rw/W-LOCK)]
                             (when-not (or (active-run) (hs/held? lk))
                               (hs/lock! lk)
                               (try
                                 (let [^objects h (g child rw/W-HOLDER)]
                                   (when (and (not (g old rw/W-COMPLETE))
                                              (not (g child rw/W-RELEASED)) (not (g child rw/W-COMPLETE))
                                              h (not (holder-dead? h))
                                              (hs/kid-move! kc t1 t2))
                                     ;; the old owner lets go: its scope's close no longer
                                     ;; releases the child, and its obligation ends
                                     (aset h 0 nil)
                                     (hs/flag-set! (aget h 2) true)
                                     (kid-done! t1)
                                     ;; queued before the child can complete (its ack is
                                     ;; queued after, FIFO); scheduled after this gate (E3)
                                     (hs/mpsc-add! (g new-owner rw/W-INGRESS)
                                                   #(hold-child! new-owner (rv new-owner (g new-owner rw/W-ROOT)) child false))
                                     (aadd! (g old rw/W-AFTER) new-owner)
                                     true))
                                 (finally (hs/unlock! lk) (handoff! child)))))))
                        ;; a released old owner refuses the host item: nothing moved
                        (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) e
                          (if (:spindel/released (ex-data e)) false (do (kid-done! t2) (throw e)))))]
            (when-not moved (kid-done! t2))
            (boolean moved)))))))

(defn world-id
  "The world's id: unique within its family (a world, its forks and
   instances share one allocator), stable for the world's life. A fork
   copies its parent's state but has its own id, so state keyed by the id
   (e.g. a wallet) does not carry over to forks (resource authority stays
   outside the engine, user decision 2026-11-17)."
  [w]
  (g w rw/ID))

(defn descendant?
  "R2: whether `w` descends from `ancestor` (a fork, a fork of a fork, an
   instance of its publication's world, ...). A world is not its own
   descendant; worlds of unrelated families never are. Ownership transfers
   change no answer."
  [w ancestor]
  (and (not (identical? w ancestor))
       (identical? (g w rw/W-FAMILY) (g ancestor rw/W-FAMILY))
       (let [a (long (g ancestor rw/ID))]
         (boolean (some #(== a (long (first %))) (g w rw/W-LINEAGE))))))

(defn fork-effect!
  "D3/Q4 `(fork)` in a task body: the fork boundary is this effect's commit.
   The parent continues with [:parent child-world]; in the child the run
   exists parked at the effect and resumes with [:child nil] (Q4)."
  [k ek]
  (if-let [refusal (finalizer-refusal)] (ek refusal)
          (if-let [r (valid-run)]
            (cond
              (comp? (rv (cw) (g r rw/R-OF)))
              (ek (ex-info "fork in a computation body is not supported" {}))
              (g (rv (cw) (g r rw/R-OF)) rw/K-LOCAL)
              (ek (invalid-op :fork-local "fork in a fork-local task: the fork would retire it (Z#77)"))
              (> (long (or (aget (ctx) 2) 0)) 1)
              (ek (ex-info "fork in a nested slice is not supported yet" {}))
              :else
              (let [w (cw)
                    owner (current-scope! w r)            ; F2: materialized before the boundary
            ;; in the child the effect is a resource its run arms, fired and acknowledged at
            ;; once: the ids in T17's order (resource, activation, wait edge)
                    _ (alloc-id! w)
                    aid (alloc-id! w)
                    _ (alloc-id! w)
                    a (new-activation! w aid r :one k ek (object-array 1) (object-array 1) 0)
                    eidx (gl r rw/R-EIDX)]
        ;; the child's view: the run resumed at the effect with its delivery
                (s! a rw/A-RESULT [[:child nil] false])
                (s! a rw/A-RESUMED true)
                (s! a rw/A-INLINE false)
                (s! r rw/R-SLICE false)
                (s! r rw/R-EIDX (inc eidx))       ; the child's run took the effect; the parent's did not
                (s! r rw/R-BIND (thread-frame))   ; the child resumes with the frame live at the effect
                (aadd! (g w rw/W-RESUME) a)
                (unregister! w a)                 ; a delivery carrier, not a parked activation
                ;; built privately: published to its family only once the fork
                ;; has committed (§8.1 F7), so no maintenance enters it before
                (let [child (fork-world* w)]
                  (own-child! w owner child true)
          ;; the parent takes the delivery back and continues on its own copy
                  (remove-row! (g w rw/W-RESUME) a)
                  (let [r (rv w r)]
                    (s! r rw/R-SLICE true)
                    (s! r rw/R-EIDX eidx)
                    (set-active! r)
                    (commit! w [:fork (g r rw/ID) (g child rw/ID)])
                    ;; a failure after the registry insertion is the published
                    ;; child's (reported); one before it leaves the committed
                    ;; child unpublished: its host admission is shut now, before
                    ;; the run gets it, and its queued T21 releases it (its
                    ;; completion acknowledges its owner scope)
                    (if (try (publish-world! child #(report! "fork publication" %)) true
                             (catch #?(:clj Throwable :cljs :default) t
                               (report! "fork publication" t) false))
            ;; scheduled after the parent's gate is released (E3)
                      (aadd! (g w rw/W-AFTER) child)
                      (do (s! child rw/W-SHUT :released)
                          (release-child! w child)))
                    (k [:parent child])))))
            (unwind! ek))))

(defn fork [] (throw (ex-info "fork outside a body" {})))

;; ---------------------------------------------------------------------------
;; Savepoints (§8.2, S1-S7)

(defn- pub-world
  "The publication's world: held strongly while its savepoint is armed,
   weakly afterwards (S9)."
  [^objects cell ww]
  (or (aget cell 0) (hs/deref-weak ww)))

(deftype Publication [^objects cell ww act site payload state local]
  ;; cell: [world (strong while pending) basis (nil once disposed)]
  #?@(:clj [clojure.lang.ILookup
            (valAt [this k] (.valAt this k nil))
            (valAt [_ k nf] (case k :world (pub-world cell ww) :act act :site site :payload payload
                                  :basis (aget cell 1) :state state :fork-local local nf))]
      :cljs [ILookup
             (-lookup [this k] (-lookup this k nil))
             (-lookup [_ k nf] (case k :world (pub-world cell ww) :act act :site site :payload payload
                                     :basis (aget cell 1) :state state :fork-local local nf))]))

(defn- let-go-world!
  "S9: a publication whose savepoint is no longer armed keeps only its basis."
  [pub]
  (aset ^objects (.-cell ^Publication pub) 0 nil))

(declare abandon-act!)

(defn- publication
  "S1: a read-only publication (no assoc, so it is never copied by accident).
   Dropping it while pending abandons its run (S7): the collection action
   holds the world, the activation id and the state, never the publication."
  [w aid site payload basis local]
  (let [state (clojure.core/atom :pending)
        ;; weakly: the world may reach the publication (a handler storing it),
        ;; and a strong reference here would keep that cycle alive forever
        ww (hs/weak w)
        p (Publication. (object-array [w basis]) ww aid site payload state local)]
    (hs/on-collect! p (fn []
                        (when (= :pending @state)
                          (when-let [w (hs/deref-weak ww)]
                            (try (abandon-act! w aid state)
                                 (catch #?(:clj Throwable :cljs :default) _ nil))))))
    p))

(defn install-handlers!
  "Merges `table` ({site handler}) into `w`'s savepoint handlers; a handler is
   called with the publication after the publishing commit (H3). `:default`
   matches every site without its own entry."
  [w table]
  (s! w rw/W-SP-HANDLERS (merge (g w rw/W-SP-HANDLERS) table))
  w)

(defn savepoint-effect!
  "S1 `(savepoint site payload)`: with a handler for `site`, the run arms a
   savepoint resource and parks on it (T17), and a publication is offered to
   the handler, holding a frozen basis of the world at this commit; without
   one the effect is the identity on `payload`. The resource has no
   controller: cancelled, it joins at once."
  [site payload k ek]
  (if-let [refusal (finalizer-refusal)] (ek refusal)
          (if-let [r (valid-run)]
            (let [w (cw)
                  handlers (g w rw/W-SP-HANDLERS)
                  h (or (get handlers site) (get handlers :default))]
              (cond
                (nil? h) (k payload)
                (comp? (rv w (g r rw/R-OF))) (ek (ex-info "savepoint in a computation body is not supported" {}))
                (> (long (or (aget (ctx) 2) 0)) 1) (ek (ex-info "savepoint in a nested slice is not supported yet" {}))
                :else
                (arm-and-park! r :savepoint k ek
                               (fn [w z]
                         ;; the basis is a fork of this commit that is never run, only forked;
                         ;; its run continues with the frame live at the effect
                                 (s! (rv w r) rw/R-BIND (thread-frame))
                                 (let [basis (fork-world* w)
                                       ;; S1: never run, never changed. Unborn (E4) before it is
                                       ;; published, so neither maintenance nor any handoff runs its
                                       ;; copied work; frozen, so no host operation reaches it
                                       ;; (activate!, swap-world!, send-world!, ...)
                                       _ (s! basis rw/W-UNBORN true)
                                       _ (s! basis rw/W-SHUT :frozen)
                                       _ (publish-world! basis)
                                       pub (publication w (id-of z) site payload basis
                                                        (boolean (g (rv w (g (rv w r) rw/R-OF)) rw/K-LOCAL)))]
                           ;; the parent's own copy of the run keeps no slice (it is parked)
                                   (set-active! (rv w r))
                                   (aadd! (g w rw/W-CALLBACKS) [(fn [_ _] (h pub)) [nil false]]))))))
            (unwind! ek))))

(defn savepoint [_ _] (throw (ex-info "savepoint outside a body" {})))

(defn- sp-res
  "The savepoint resource `zid` as `w` holds it while armed: its own row, or
   one it inherited (dormant)."
  [w zid]
  (let [zid (long zid)
        z (some #(when (== (id-of %) zid) %)
                (concat (some-> (g w rw/W-ARMED) hs/oset-vals) (g w rw/W-DORMANT)))]
    (when z
      (let [z (rv w z)] (when (== rw/Z-ARMED (gl z rw/Z-PHASE)) z)))))

(defn- sp-fire!
  "S2/S4 = T18 then T15: the savepoint fires `ok v` and joins."
  [w zid v]
  (if-let [z (sp-res w zid)]
    (do (resource-fire! w z [v false]) (resource-ack! w z))
    (refuse! w [:resource-fire zid])))

(defn resume!
  "S2: continues the publication's own world with `v`, at most once."
  [pub v]
  (let [w (:world pub)]
    (when (compare-and-set! (:state pub) :pending :resumed)
      (let-go-world! pub)
      (gated w (sp-fire! w (:act pub) v)))
    nil))

(defn- abandon-act!
  "S7 = T14: the run parked on the savepoint is cancelled; the resource joins
   at once."
  [w zid state]
  (when (compare-and-set! state :pending :abandoned)
    (gated w
           (if-let [z (sp-res w zid)]
             (let [r (rv w (g z rw/OWNER))]
               (cancel! w r ::abandoned)
               (commit! w [:cancel (g r rw/ID)]))
             (refuse! w [:cancel zid]))))
  nil)

(defn abandon!
  "S7: cancels the run suspended at the publication with err ::abandoned."
  [pub]
  (when-let [w (:world pub)]
    (abandon-act! w (:act pub) (:state pub)))
  (when-not (= :pending @(:state pub)) (let-go-world! pub))
  nil)

(defn instantiate
  "S3: a frozen fork of the publication's basis, not yet activated: the
   run's copy is parked on its savepoint, which is the fork's pending
   activation. Any number of instances are independent. `owner` (default:
   the publication's world) is the world whose root scope owns the instance
   once it is activated; it must be of the same family. `init-state`
   (state -> state) sets the instance's world state before anyone can reach
   it."
  ([pub] (instantiate pub nil nil))
  ([pub owner] (instantiate pub owner nil))
  ([pub owner init-state]
   (let [b (or (:basis pub)
               (throw (ex-info "instantiate: the publication is disposed" {:spindel/invalid :disposed})))
         owner (or owner (:world pub)
                   (throw (ex-info "instantiate: the publication's world is gone; name an owner"
                                   {:spindel/invalid :owner})))]
     (when-not (identical? (g owner rw/W-FAMILY) (g b rw/W-FAMILY))
       (throw (ex-info "instantiate: the owner belongs to an unrelated world" {:spindel/invalid :lineage})))
     (when (:fork-local pub)
       (throw (invalid-op :fork-local "instantiate: the run is fork-local, every instance would retire it (Z#77)")))
     ;; nobody else can reach the instance yet: its initial state is set
     ;; directly, without a host item (so also from another world's slice),
     ;; and computed before anything is allocated
     (let [st (if init-state (init-state (g b rw/W-STATE)) (g b rw/W-STATE))
           c (instance-world* b (:act pub) owner st)]
       ;; published with every birth field set: the family's maintenance
       ;; can enter it from here on, and finds it unborn
       (publish-world! c)
       c))))

(defn consume
  "S8: continues the run suspended at the publication only in `k` new
   instances (owned by `owner`, default the publication's world), never in
   its own world: its savepoint is consumed, so it can no longer be resumed
   or abandoned, and its finalizers never run there. Refused (throws, the
   publication stays pending) unless the savepoint is armed and the run
   holds no other resource (S6). `init-of` (index -> init-state, see
   `instantiate`) sets each instance's initial state. Returns the
   instances, unborn."
  ([pub k] (consume pub k nil nil))
  ([pub k owner] (consume pub k owner nil))
  ([pub k owner init-of]
   (let [w (or (:world pub) (throw (ex-info "consume: the savepoint is not pending" {:spindel/invalid :consume})))
         owner (or owner w)]
     (host-call! w #(let [z (sp-res w (:act pub))
                          r (when z (rv w (g z rw/OWNER)))
                          res (when r (g r rw/R-RES))]
                      (cond
                        (or (nil? z) (not= :pending @(:state pub)))
                        (do (refuse! w [:consume (:act pub)])
                            (throw (ex-info "consume: the savepoint is not pending" {:spindel/invalid :consume})))
                        (:fork-local pub)
                        (do (refuse! w [:consume (:act pub)])
                            (throw (invalid-op :fork-local "consume: the run is fork-local, every instance would retire it (Z#77)")))
                        (and res (> (acount res) 1))
                        (do (refuse! w [:consume (:act pub)])
                            (throw (ex-info "consume: the run holds resources besides its savepoint (S6)"
                                            {:spindel/invalid :consume})))
                        :else
                        (do (reset! (:state pub) :consumed)
                            ;; its continuation lives on in the instances only
                            (s! r rw/R-FINS 0)
                            (commit! w [:consume (:act pub) k])))))
     (let [is (mapv (fn [i] (instantiate pub owner (when init-of (init-of i)))) (range k))]
       (let-go-world! pub)
       is))))

(defn dispose!
  "S9: ends a publication used as an anchor. A pending one is abandoned
   first (S7); then it drops its basis and its world. Instantiating it
   afterwards is refused."
  [pub]
  (when (= :pending @(:state pub)) (abandon! pub))
  (let [^objects cell (.-cell ^Publication pub)]
    (aset cell 0 nil)
    (aset cell 1 nil))
  nil)

(defn activate!
  "S4: resumes an instantiated fork's pending activation with `v`. The fork
   is born here: the root scope of its owner (`instantiate`) owns it (F2)."
  [w v]
  (gated w
         (when-let [pw (g w rw/W-PUB-WORLD)]
           (s! w rw/W-PUB-WORLD nil)
      ;; F2: the owner's table is the publication world's; its gate is only
      ;; tried, never waited for. A released owner releases the instance.
           (try (host! pw #(own-child! pw (rv pw (g pw rw/W-ROOT)) w false))
                (catch #?(:clj Exception :cljs :default) _
                  (release-world* w))))                 ; still unborn: nothing runs
         (let [zid (when-not (g w rw/W-RELEASED) (g w rw/W-PENDING-ACT))
               born? (and (g w rw/W-UNBORN) (not (g w rw/W-RELEASED)))]
           (when born? (s! w rw/W-UNBORN false))
           ;; the pending savepoint fires first, while it is still dormant
           (when zid
             (s! w rw/W-PENDING-ACT nil)
             (sp-fire! w zid v))
           ;; the other inherited resources: this item is the first turn's
           ;; work, so they are settled here, not at a later turn entry
           (when (and born? (or (g w rw/W-DORMANT) (g w rw/W-DISCHARGE))) (activate-dormant! w))
           (when (and born? (g w rw/W-NORMALIZE)) (normalize! w))))
  w)

(defn offload [& _] (throw (ex-info "offload outside a body" {})))

(defn external [_] (throw (ex-info "external outside a body" {})))
(defn await-op [& _] (throw (ex-info "await-op outside a body" {})))

(defn sleep [_] (throw (ex-info "sleep outside a body" {})))

(defn track [_] (throw (ex-info "track outside a body" {})))
(defn await [_] (throw (ex-info "await outside a body" {})))
(defn await-all [_] (throw (ex-info "await-all outside a body" {})))
(defn take! [_] (throw (ex-info "take! outside a body" {})))
(defn acquire! [_] (throw (ex-info "acquire! outside a body" {})))
(defn await-any [_] (throw (ex-info "await-any outside a body" {})))

;; ---------------------------------------------------------------------------
;; Custom effects (M6 R3): a handler returns an op, the engine executes it;
;; handlers never see continuations.

(defonce ^:private effect-handlers (clojure.core/atom {}))

;; the captured values of a body that captures none: the expansion of `spin`
;; and `task` refers to it, so it exists on both platforms
(def empty-inputs (object-array 0))

#?(:clj (defonce ^:private extra-breakpoints (clojure.core/atom {})))

(defn register-effect!
  "R3: makes `sym` (qualified) an effect of spin/task bodies. `handler` is
   `(fn [args ctx] op)`, called inside the slice; `ctx` is {:effect :site
   :run :effect-index}, `:site` stable per call site. `op` is one of
   [:value v], [:error e], [:external f] (R2), [:savepoint site payload]
   (S1, multi-shot) or [:await h]. Bodies compiled before the registration
   do not see the effect."
  [sym handler]
  (swap! effect-handlers assoc sym handler)
  #?(:clj (swap! extra-breakpoints assoc sym `bp-custom))
  sym)

(defn custom-effect!
  [sym args site k ek]
  (if-let [refusal (finalizer-refusal)]
    (ek refusal)
    (if-let [r (valid-run)]
      (let [h (or (get @effect-handlers sym)
                  (throw (ex-info "unregistered effect" {:spindel/invalid :effect :effect sym})))
          ;; §8.2 addresses: counted on entry, before a savepoint freezes the run
            key (effect-key! r site)
            op (try (h args {:effect sym :site site :run (g r rw/ID) :effect-index (gl r rw/R-EIDX)
                             :key key :frame (frame-of (rv (cw) (g r rw/R-OF))) :path (g r rw/R-PATH)})
                    (catch #?(:clj Throwable :cljs :default) t [:error t]))]
        (case (when (vector? op) (first op))
          :value (k (nth op 1))
          :error (ek (nth op 1))
          :external (external-effect! (nth op 1) k ek)
          :savepoint (savepoint-effect! (nth op 1) (nth op 2) k ek)
          :await (await-effect! (row-of (nth op 1)) k ek)
          (ek (ex-info "an effect handler returned no op" {:spindel/invalid :effect :effect sym :op op}))))
      (unwind! ek))))

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
       (fn [[f opts]] `(offload-effect! ~f ~opts ~r ~e)))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-await-op [_ctx r e]
       (fn [[op opts]] `(await-op-effect! ~op ~opts ~r ~e)))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-external [_ctx r e]
       (fn [[f]] `(external-effect! ~f ~r ~e)))
     (declare site-of)
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-custom [ctx r e]
       (let [form (:form ctx)
             sym (ioc/var-name (:env ctx) (first form))
             site (site-of form)]
         (fn [args] `(custom-effect! '~sym [~@args] ~site ~r ~e))))
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
        'org.replikativ.spindel.v2.core/external `bp-external
        'org.replikativ.spindel.v2.core/await-op `bp-await-op
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
                      (not (#{'org.replikativ.spindel.v2.core/with-scope 'org.replikativ.spindel.v2.core/with-path}
                            (symbol (str (.-ns ^clojure.lang.Var v)) (str (.-sym ^clojure.lang.Var v))))))
             v))))
     (defn- var-key
       "A stable key for dynamic var `v` (its qualified name) in `env`."
       [env v]
       (keyword (str (or (ioc/var-name env v) v))))
     (defn- cljs-binding?
       "A CLJS `binding` (not a local of that name): B10 keeps it in the run."
       [h]
       (and (:ns *env*) (#{'binding 'cljs.core/binding} h)
            (not (contains? (:locals *env*) h))))
     (defn- cljs-binding
       "CLJS `binding` in a body: the vars are bound in the running run, so
        the binding survives effects and slice! sets and restores them."
       [[_ bvec & body :as form]]
       (let [saved (gensym "bindings")]
         (with-meta
           `(let [~saved (push-bindings!
                          [~@(doall (for [[v e] (partition 2 bvec)]
                                      `[~(var-key *env* v) (fn [] ~v) (fn [x#] (set! ~v x#)) ~(register-finally e)]))])]
              (~'try (do (enter-finally!) ~@(mapv register-finally body))
                     (~'finally (exit-finally!) (~'try (pop-bindings! ~saved) (~'finally (leave-finalizer!))))))
           (meta form))))
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
             (cljs-binding? h) (cljs-binding form)
             (opaque-head? h) form
             (and expanded (has-finally? expanded)) (register-finally expanded)
             (= 'try h)
             (let [clauses (mapv register-finally (rest form))   ; eager: *env* is bound only here
                   [body cfs] (split-with (complement catch-or-finally?) clauses)]
               (if (some #(= 'finally (first %)) cfs)
                 (with-meta
                   `(~'try (do (enter-finally!) ~@body)
                           ~@(map (fn [c] (if (= 'finally (first c))
                                            (list 'finally `(exit-finally!)
                                                  (list 'try (cons 'do (rest c)) (list 'finally `(leave-finalizer!))))
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
             params {:r r :e e :env env :breakpoints (merge breakpoints @extra-breakpoints)
                     :opaque-scopes #{`spin `task}}]
         `(fn [~r ~e] ~(ioc/invert params (binding [*env* env] (register-finally (cons 'do body)))))))
     (defn- inputs-form
       "The captured values as an array, built without an intermediate vector."
       [frees]
       (if (empty? frees)
         `empty-inputs
         (let [a (with-meta (gensym "in") {:tag 'objects})]
           `(let [~a (object-array ~(count frees))]
              ~@(map-indexed (fn [i x] `(aset ~a ~i ~x)) frees)
              ~a))))
     (defn effectful?
       "Macro time (A3): whether `form` performs an effect in its own scope:
        calls a v2 breakpoint or a registered effect (`defeffect`), looked
        up through `env`, locals first. Nested bodies, closures and quoted
        forms are not its scope (see `macro-support/some-call`)."
       [env form]
       (let [effects (merge breakpoints @extra-breakpoints)]
         (boolean (ms/some-call env form (fn [env x] (contains? effects (ms/head-name env (first x))))))))
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
                   (~'finally (exit-finally!) (~'try (close-scope-fx! ~s) (~'finally (leave-finalizer!))))))))
     (defmacro convey
       "B10: host-level `binding`s of dynamic var `v` reach the tasks and
        computations created under them. JVM: every binding does; no-op. CLJS:
        only declared vars (bindings inside bodies need no declaration)."
       [v]
       (when (:ns &env)
         `(register-conveyed! ~(var-key &env v) (fn [] ~v) (fn [x#] (set! ~v x#)))))
     (defmacro with-path
       "§8.2 P1-P6: labels the effect sites reached in `body` with the vector
        `p` appended to the run's path; a registered effect receives the path
        in its context (`:path`), and tasks and computations created inside
        inherit it. Restored when `body` exits, however it exits. Outside a
        body it runs `body` unlabeled."
       [p & body]
       (let [saved (gensym "path")]
         `(let [~saved (push-path! ~p)]
            (~'try (do (enter-finally!) ~@body)
                   (~'finally (exit-finally!) (~'try (pop-path! ~saved) (~'finally (leave-finalizer!))))))))
     (defmacro with-key
       "§5.2 (Z#82): the creations in `body` (also in the functions it calls),
        in the running run, have the creation key [site K n]: K the keys of
        the active `with-key` forms, outermost first, `n` the run's earlier
        creations with the same site and K. A computation run adopts the
        predecessor with the same key, in any order. `k` is an immutable
        value, compared by value, evaluated once before `body`. `body` runs
        synchronously: an effect in it does not compile; the computations and
        tasks it creates run in their own scopes. Outside a body it runs
        `body` unkeyed."
       [k & body]
       `(with-key* ~k (fn [] ~@body)))
     (defmacro defeffect
       "R3: defines effect `name` in this namespace: `(defeffect choose [args
        ctx] op-form)`; see register-effect!. It registers at expansion too,
        so later bodies in the same file see it."
       [name [args ctx] & body]
       (let [sym (symbol (str *ns*) (str name))]
         (swap! extra-breakpoints assoc sym `bp-custom)
         `(do (defn ~name [& _#] (throw (ex-info ~(str name " outside a body") {})))
              (register-effect! '~sym (fn [~args ~ctx] ~@body)))))
     (defmacro task
       "A task (T4): started at once; structured child of the creating run."
       [& body]
       (let [frees (vec (sort-by str (filter symbol? (free-vars/free-variables-or-all &env (cons 'do body)))))]
         `(spawn! ~(site-of &form) ~(inputs-form frees) ~(body-fn &env body))))
     (defmacro task-with
       "`task` with options, a map evaluated at run time. `{:fork-local true}`
        (Z#77): the task, and every task its runs create under their scopes,
        is retired in every fork of the world without running anything (no
        finalizer); its waiters there get ::forked with :spindel/fork-local.
        Refused inside a computation."
       [opts & body]
       (let [frees (vec (sort-by str (filter symbol? (free-vars/free-variables-or-all &env (cons 'do body)))))]
         `(spawn! ~(site-of &form) ~(inputs-form frees) ~(body-fn &env body) ~opts)))
     (defmacro body*
       "A body (fn [ok err]) compiled like a spin's, in the enclosing scope."
       [& body]
       (body-fn &env body))
     (defmacro aseq
       "A pull sequence (C0): `(aseq [s init] body...)`. For state `s` the body
        returns `[v s']` (the element and the next state) or nil (the end); it
        may await. Elements are realized on first read, once per world, and
        shared by every reader. Returns the head position."
       [[s init] & body]
       (let [frees (vec (sort-by str (filter symbol? (free-vars/free-variables-or-all
                                                      &env (list 'fn [s] (cons 'do body))))))]
         `(new-aseq-at ~(site-of &form) ~(inputs-form frees) (fn [~s] (body* ~@body)) ~init)))))
