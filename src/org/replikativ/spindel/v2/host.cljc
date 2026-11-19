(ns org.replikativ.spindel.v2.host
  "Platform layer for engine v2: the few host structures the core needs, with
   one JVM and one JS implementation each. JS is single-threaded, so the gate
   is a flag and the drainer is a macrotask.")

;; ---------------------------------------------------------------------------
;; Maps: identity maps (rows as keys) and value maps (ints, values)

(defn imap [] #?(:clj (java.util.IdentityHashMap.) :cljs (js/Map.)))
(defn vmap [] #?(:clj (java.util.HashMap.) :cljs (js/Map.)))
(defn lmap "Insertion-ordered." [] #?(:clj (java.util.LinkedHashMap.) :cljs (js/Map.)))

(defn mget [m k] #?(:clj (.get ^java.util.Map m k) :cljs (.get m k)))
(defn mput! [m k v] #?(:clj (.put ^java.util.Map m k v) :cljs (.set m k v)) nil)
(defn mdel! [m k] #?(:clj (.remove ^java.util.Map m k) :cljs (.delete m k)) nil)
(defn msize [m] #?(:clj (.size ^java.util.Map m) :cljs (.-size m)))
(defn mclear! [m] #?(:clj (.clear ^java.util.Map m) :cljs (.clear m)) nil)
(defn mkeys [m] #?(:clj (vec (.keySet ^java.util.Map m)) :cljs (vec (es6-iterator-seq (.keys m)))))
(defn mvals [m] #?(:clj (vec (.values ^java.util.Map m)) :cljs (vec (es6-iterator-seq (.values m)))))
(defn mentries [m]
  #?(:clj (mapv (fn [^java.util.Map$Entry e] [(.getKey e) (.getValue e)]) (.entrySet ^java.util.Map m))
     :cljs (mapv vec (es6-iterator-seq (.entries m)))))

;; ---------------------------------------------------------------------------
;; Lists (ArrayList / array): the operations rows.cljc's macros do not cover

(defn index-of [l x] #?(:clj (.indexOf ^java.util.ArrayList l x) :cljs (.indexOf l x)))
(defn last-index-of [l x] #?(:clj (.lastIndexOf ^java.util.ArrayList l x) :cljs (.lastIndexOf l x)))
(defn remove-at! [l i] #?(:clj (.remove ^java.util.ArrayList l (int i)) :cljs (.splice l i 1)) nil)
(defn remove-first! [l] #?(:clj (.remove ^java.util.ArrayList l (int 0)) :cljs (.shift l)))
(defn remove-value! [l x]
  (let [i (index-of l x)] (when-not (neg? i) (remove-at! l i) true)))

;; ---------------------------------------------------------------------------
;; FIFO deques (mailbox queues, waiters) and the ingress queue (H1)

(defn deque [] #?(:clj (java.util.ArrayDeque.) :cljs (array)))
(defn dq-push! [q x] #?(:clj (.addLast ^java.util.ArrayDeque q x) :cljs (.push q x)) nil)
(defn dq-poll! [q] #?(:clj (.pollFirst ^java.util.ArrayDeque q) :cljs (.shift q)))
(defn dq-empty? [q] #?(:clj (.isEmpty ^java.util.ArrayDeque q) :cljs (zero? (.-length q))))
(defn dq-remove-if!
  "Removes the elements `x` of deque `q` with `(pred x)`."
  [q pred]
  #?(:clj (.removeIf ^java.util.ArrayDeque q (reify java.util.function.Predicate (test [_ x] (boolean (pred x)))))
     :cljs (loop [i (dec (.-length q))]
             (when-not (neg? i)
               (when (pred (aget q i)) (.splice q i 1))
               (recur (dec i)))))
  nil)

(defn mpsc [] #?(:clj (java.util.concurrent.ConcurrentLinkedQueue.) :cljs (array)))
(defn mpsc-add! [q x] #?(:clj (.add ^java.util.concurrent.ConcurrentLinkedQueue q x) :cljs (.push q x)) nil)
(defn mpsc-poll! [q] #?(:clj (.poll ^java.util.concurrent.ConcurrentLinkedQueue q) :cljs (.shift q)))
(defn mpsc-empty? [q] #?(:clj (.isEmpty ^java.util.concurrent.ConcurrentLinkedQueue q) :cljs (zero? (.-length q))))

;; ---------------------------------------------------------------------------
;; Flags, the gate lock (H2), scheduling

(defn flag [v] #?(:clj (java.util.concurrent.atomic.AtomicBoolean. (boolean v)) :cljs #js {:v (boolean v)}))
(defn flag-cas! [f old new]
  #?(:clj (.compareAndSet ^java.util.concurrent.atomic.AtomicBoolean f (boolean old) (boolean new))
     :cljs (if (= (.-v ^js f) old) (do (set! (.-v ^js f) new) true) false)))
(defn flag? [f] #?(:clj (.get ^java.util.concurrent.atomic.AtomicBoolean f) :cljs (.-v ^js f)))
(defn flag-set! [f v] #?(:clj (.set ^java.util.concurrent.atomic.AtomicBoolean f (boolean v)) :cljs (set! (.-v ^js f) v)) nil)
;; A world's child-completion obligations (C1 R2): a count changed from any
;; thread, and a released flag, both sequentially consistent, so a child's
;; decrement to zero and its owner's release never both miss each other.
(defn kids [] #?(:clj (object-array [(java.util.concurrent.atomic.AtomicLong. 0) (flag false)])
                 :cljs (object-array [#js {:v 0} (flag false)])))
(defn kids-add! [k d]
  #?(:clj (.addAndGet ^java.util.concurrent.atomic.AtomicLong (aget ^objects k 0) (long d))
     :cljs (let [c (aget k 0)] (set! (.-v c) (+ (.-v c) d)) (.-v c))))
(defn kids-count [k]
  #?(:clj (.get ^java.util.concurrent.atomic.AtomicLong (aget ^objects k 0)) :cljs (.-v (aget k 0))))
(defn kids-released! [k] (flag-set! (aget ^objects k 1) true))
(defn kids-released? [k] (flag? (aget ^objects k 1)))
;; A fork's link to its owner (C1 R2), one atomic reference: nil, then the
;; owner's token (accepted) or :done (the world completed or was collected).
;; Whichever of acceptance and completion comes second acknowledges.
(defn kid-cell [] #?(:clj (java.util.concurrent.atomic.AtomicReference.) :cljs #js {:v nil}))
(defn kid-accept!
  "Installs token `t`; false when the world was already done."
  [c t]
  #?(:clj (.compareAndSet ^java.util.concurrent.atomic.AtomicReference c nil t)
     :cljs (if (nil? (.-v c)) (do (set! (.-v c) t) true) false)))
(defn kid-token
  "The installed token, :done, or nil."
  [c]
  #?(:clj (.get ^java.util.concurrent.atomic.AtomicReference c) :cljs (.-v c)))
(defn kid-move!
  "C2 transfer: replaces the installed token `old` by `new`; false when the
   world was done (or `old` is not installed)."
  [c old new]
  #?(:clj (.compareAndSet ^java.util.concurrent.atomic.AtomicReference c old new)
     :cljs (if (identical? (.-v c) old) (do (set! (.-v c) new) true) false)))
(defn kid-finish!
  "Marks the world done; returns the token installed before, if any."
  [c]
  #?(:clj (let [old (.getAndSet ^java.util.concurrent.atomic.AtomicReference c :done)] (when-not (keyword? old) old))
     :cljs (let [old (.-v c)] (set! (.-v c) :done) (when-not (keyword? old) old))))

(defn lock [] #?(:clj (java.util.concurrent.locks.ReentrantLock.) :cljs #js {:held false}))
(defn held? [lk] #?(:clj (.isHeldByCurrentThread ^java.util.concurrent.locks.ReentrantLock lk) :cljs (.-held ^js lk)))
(defn try-lock! [lk]
  #?(:clj (.tryLock ^java.util.concurrent.locks.ReentrantLock lk)
     :cljs (if (.-held ^js lk) false (do (set! (.-held ^js lk) true) true))))
(defn lock!
  "Waits for the lock. Only where no cycle can form: the caller holds no gate
   a holder of `lk` could wait for (B7)."
  [lk]
  #?(:clj (.lock ^java.util.concurrent.locks.ReentrantLock lk)
     :cljs (if (.-held ^js lk) (throw (js/Error. "lock! on a held gate")) (set! (.-held ^js lk) true)))
  nil)
(defn unlock! [lk] #?(:clj (.unlock ^java.util.concurrent.locks.ReentrantLock lk) :cljs (set! (.-held ^js lk) false)) nil)

#?(:clj (def default-executor
          (delay (java.util.concurrent.Executors/newVirtualThreadPerTaskExecutor))))

(defn executor [] #?(:clj @default-executor :cljs nil))

(defn execute-or!
  "execute!, calling `(on-reject t)` instead of throwing when the executor
   refuses the work."
  [ex on-reject f]
  #?(:clj (try (.execute ^java.util.concurrent.Executor ex ^Runnable f)
               (catch java.util.concurrent.RejectedExecutionException t (on-reject t)))
     :cljs (js/setTimeout f 0))
  nil)

(defn execute!
  "Runs `f` later: on the executor (JVM), as a macrotask (JS)."
  [ex f]
  #?(:clj (.execute ^java.util.concurrent.Executor ex ^Runnable f)
     :cljs (js/setTimeout f 0))
  nil)

#?(:clj
   (def ^:private metadata-executor
     (delay (java.util.concurrent.ScheduledThreadPoolExecutor.
             1 (reify java.util.concurrent.ThreadFactory
                 (newThread [_ r]
                   (doto (Thread. ^Runnable r "spindel-v2-metadata") (.setDaemon true))))))))

(defn metadata-later!
  "Dedicated asynchronous metadata dispatch. Never uses an inline/user
   executor; retries never block a world gate or drain engine work."
  ([f] (metadata-later! f 0))
  ([f delay-ms]
   #?(:clj (.schedule ^java.util.concurrent.ScheduledExecutorService @metadata-executor
                      ^Runnable f (long delay-ms) java.util.concurrent.TimeUnit/MILLISECONDS)
      :cljs (js/setTimeout f delay-ms))
   nil))

(defn fence! [x] #?(:clj (java.lang.ref.Reference/reachabilityFence x) :cljs nil))

;; ---------------------------------------------------------------------------
;; Weak handles (§1): a weak reference and a collection callback

#?(:clj (def ^:private cleaner (delay (java.lang.ref.Cleaner/create)))
   :cljs (def ^:private registry
           (when (exists? js/FinalizationRegistry)
             (js/FinalizationRegistry. (fn [f] (f))))))

(defn on-collect!
  "Calls `f` after `x` is collected. `f` must not reference `x`."
  [x f]
  #?(:clj (.register ^java.lang.ref.Cleaner @cleaner x ^Runnable f)
     :cljs (when registry (.register registry x f)))
  nil)

(defn weak [x] #?(:clj (java.lang.ref.WeakReference. x) :cljs (when (exists? js/WeakRef) (js/WeakRef. x))))
(defn deref-weak [r]
  (when r #?(:clj (.get ^java.lang.ref.WeakReference r) :cljs (.deref r))))

;; ---------------------------------------------------------------------------
;; Timers

#?(:clj
   (def ^:private timer-exec
     (delay (doto (java.util.concurrent.ScheduledThreadPoolExecutor.
                   1 (reify java.util.concurrent.ThreadFactory
                       (newThread [_ r] (doto (Thread. ^Runnable r "spindel-v2-timer") (.setDaemon true)))))
              (.setRemoveOnCancelPolicy true)))))

#?(:clj (deftype Timer [^java.util.concurrent.atomic.AtomicBoolean claimed fut]))

(defn schedule!
  "Runs `f` after `ms`; returns a token for `unschedule!`. JVM: the callback
   and `unschedule!` race for one claim, so exactly one of them wins."
  [ms f]
  #?(:clj (let [claimed (java.util.concurrent.atomic.AtomicBoolean. false)
                run (fn [] (when (.compareAndSet claimed false true) (f)))]
            (Timer. claimed (.schedule ^java.util.concurrent.ScheduledExecutorService @timer-exec
                                       ^Runnable run (long ms) java.util.concurrent.TimeUnit/MILLISECONDS)))
     :cljs (js/setTimeout f ms)))

(defn unschedule!
  "True when the timer will not fire: `f` has not started and never will.
   JVM: `Future.cancel` also answers true while the callback is running (the
   future is not done yet), so the answer is the claim, not the cancel."
  [t]
  #?(:clj (let [^Timer t t]
            (when (.compareAndSet ^java.util.concurrent.atomic.AtomicBoolean (.-claimed t) false true)
              (.cancel ^java.util.concurrent.Future (.-fut t) false)
              true))
     :cljs (do (js/clearTimeout t) true)))

(defn timer? [t]
  #?(:clj (instance? Timer t) :cljs (number? t)))

;; ---------------------------------------------------------------------------
;; Offload control (JVM threads; JS runs the function as a macrotask)

(defn offload-ctl [] #?(:clj {:state (java.util.concurrent.atomic.AtomicInteger. 0) :thread (volatile! nil)}
                        :cljs {:state #js {:v 0}}))

(defn ctl-start!
  "0 -> 1: the function may run now."
  [{:keys [state thread]}]
  #?(:clj (when (.compareAndSet ^java.util.concurrent.atomic.AtomicInteger state 0 1)
            (vreset! thread (Thread/currentThread))
            true)
     :cljs (when (zero? (.-v ^js state)) (set! (.-v ^js state) 1) true)))

(defn ctl-finish! [{:keys [thread]}]
  #?(:clj (do (vreset! thread nil) (Thread/interrupted)) :cljs nil)
  nil)

(defn ctl-cancel!
  "True when the function never started (it now never will); otherwise the
   running function is interrupted (JVM) and joins when it returns."
  [{:keys [state thread]}]
  #?(:clj (if (.compareAndSet ^java.util.concurrent.atomic.AtomicInteger state 0 2)
            true
            (do (some-> ^Thread @thread .interrupt) false))
     :cljs (if (zero? (.-v ^js state)) (do (set! (.-v ^js state) 2) true) false)))

;; ---------------------------------------------------------------------------
;; Insertion-ordered sets of rows keyed by row ID (scope task lists): O(1) add
;; and remove; identity is the stable ID, so a row and its copy in a forked
;; world are the same member (M5).

(defn oset [] #?(:clj (java.util.LinkedHashMap.) :cljs (js/Map.)))
(defn oset-add! [s id x] #?(:clj (.put ^java.util.LinkedHashMap s id x) :cljs (.set s id x)) nil)
(defn oset-del! [s id] #?(:clj (some? (.remove ^java.util.LinkedHashMap s id)) :cljs (.delete s id)))
(defn oset-get [s id] #?(:clj (.get ^java.util.LinkedHashMap s id) :cljs (.get s id)))
(defn oset-count [s] #?(:clj (.size ^java.util.LinkedHashMap s) :cljs (.-size s)))
(defn oset-vals "A snapshot vector, in insertion order." [s]
  #?(:clj (vec (.values ^java.util.LinkedHashMap s)) :cljs (vec (es6-iterator-seq (.values s)))))
(defn oset-copy [s] #?(:clj (java.util.LinkedHashMap. ^java.util.Map s) :cljs (js/Map. s)))

(defn mcopy "A shallow copy of a host map." [m]
  #?(:clj (cond (instance? java.util.IdentityHashMap m) (java.util.IdentityHashMap. ^java.util.Map m)
                (instance? java.util.LinkedHashMap m) (java.util.LinkedHashMap. ^java.util.Map m)
                :else (java.util.HashMap. ^java.util.Map m))
     :cljs (js/Map. m)))
(defn lcopy "A shallow copy of a list." [l] #?(:clj (java.util.ArrayList. ^java.util.Collection l) :cljs (.slice l)))
(defn dcopy "A shallow copy of a deque." [q] #?(:clj (java.util.ArrayDeque. ^java.util.Collection q) :cljs (.slice q)))

(defn now-ms [] #?(:clj (System/currentTimeMillis) :cljs (.now js/Date)))
