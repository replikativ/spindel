(ns org.replikativ.spindel.v2.rows
  "Row layouts for engine v2 (docs/engine-v2-spec.md §2, §10.1).

   Rows are object arrays with named field indices. Every row starts with
   TYPE and ID. Debtor rows (computations, sources, tasks) share the fields
   WORLD..AT so edge code is kind-independent.")

#?(:clj
   (do
     (defn cljs? [env] (some? (:ns env)))
     (defmacro g [row i]
       (let [s (with-meta (gensym "row") {:tag 'objects})]
         `(let [~s ~row] (aget ~s ~i))))
     ;; -Dspindel.v2.check-writes=true (tests): every row write first checks
     ;; that the processed world owns the row (fork isolation, §8.1). Read at
     ;; macro expansion, so production code has no check.
     (def ^:private check-writes? (Boolean/getBoolean "spindel.v2.check-writes"))
     (defmacro s! [row i v]
       (let [s (with-meta (gensym "row") {:tag 'objects})
             chk (when (and check-writes? (not (cljs? &env)))
                   `(check-owned! ~s ~i))]
         (if (cljs? &env)
           `(let [~s ~row] (aset ~s ~i ~v))
           `(let [~s ~row] ~chk (clojure.lang.RT/aset ~s (int ~i) (clojure.lang.RT/box ~v))))))
     (defmacro gl [row i] `(long (g ~row ~i)))
     (defmacro gm
       "A row's container (list, map, deque, array) fetched to be mutated: in
        test builds (check-writes) the processed world must own the row."
       [row i]
       (if (and check-writes? (not (cljs? &env)))
         (let [s (with-meta (gensym "row") {:tag 'objects})]
           `(let [~s ~row] (check-owned! ~s ~i) (aget ~s ~i)))
         `(g ~row ~i)))
     (defn- al [] (with-meta (gensym "l") {:tag 'java.util.ArrayList}))
     (defmacro alist [] (if (cljs? &env) `(cljs.core/array) `(java.util.ArrayList. 4)))
     (defmacro acount [l] (if (cljs? &env) `(.-length ~l) (let [x (al)] `(let [~x ~l] (.size ~x)))))
     (defmacro anth [l i] (if (cljs? &env) `(aget ~l ~i) (let [x (al)] `(let [~x ~l] (.get ~x (int ~i))))))
     (defmacro aadd! [l v] (if (cljs? &env) `(.push ~l ~v) (let [x (al)] `(let [~x ~l] (.add ~x (clojure.lang.RT/box ~v))))))
     (defmacro apop! [l] (if (cljs? &env) `(.pop ~l)
                             (let [x (al)] `(let [~x ~l] (.remove ~x (int (dec (.size ~x))))))))
     (defmacro aput! [l i v] (if (cljs? &env) `(aset ~l ~i ~v)
                                 (let [x (al)] `(let [~x ~l] (.set ~x (int ~i) (clojure.lang.RT/box ~v))))))
     (defmacro aclear! [l] (if (cljs? &env) `(set! (.-length ~l) 0)
                               (let [x (al)] `(let [~x ~l] (.clear ~x)))))
     (defmacro acopy [l] (if (cljs? &env) `(.slice ~l)
                             (let [x (al)] `(let [~x ~l] (java.util.ArrayList. ~x)))))))

;; M5 owner epochs: every row has one extra last slot holding the epoch of the
;; world incarnation that owns it.
;; MVCC forks (v2-fork-memory-design): an epoch names its world and an
;; ordinal that advances at each fork the world makes. The world that owns a
;; row (its epoch stamps it) changes it in place; before its first change after
;; a fork it saves the row's state as a version on the row, for the forks that
;; may still read it (`[k m image]`: the state seen by forks with ordinal k..m).
(deftype Epoch [world ^long ordinal])
(defn epoch [world ordinal] (Epoch. world ordinal))
(defn epoch-world [^Epoch e] (.-world e))
(defn epoch-ordinal ^long [^Epoch e] (.-ordinal e))

;; A fork's claim on its owner's versions at ordinal `ordinal`: held strongly
;; by the lineage of the fork and its descendants; the owner lists its cell
;; `[ordinal state rows owner]` (state :live, :shared or :dead). It ends when
;; collected, or earlier when its fork has finished and nothing was derived
;; from it (`shared` is sticky).
(deftype Token [^long ordinal cell])
(defn token [o cell] (Token. o cell))
(defn token-cell [^Token t] (.-cell t))
(defn token-dead? [^Token t] (identical? :dead (aget ^objects (.-cell t) 1)))
(defn token-share! [^Token t]
  (let [^objects c (.-cell t)] (when (identical? :live (aget c 1)) (aset c 1 :shared))) nil)
(defn token-finish!
  "Ends the token unless it was shared (called by its own world, serially
   with token-share!). True when it ended now."
  [^Token t]
  (let [^objects c (.-cell t)]
    (when (identical? :live (aget c 1)) (aset c 1 :dead) true)))

#?(:clj
   (defmacro locking-row
     "The per-row monitor of the version protocol (a no-op on CLJS)."
     [r & body]
     (if (cljs? &env) `(do ~@body) `(locking ~r ~@body))))

(defn new-row
  "A row of `size` fields plus three trailing slots: the ID of the world that
   created it (copies keep it; handle lineage, §8.1), its saved versions, and
   its owner epoch (always the last slot)."
  ^objects [epoch creator size]
  (let [a (object-array (+ 3 (long size)))]
    (aset a (long size) creator)
    (aset a (+ 2 (long size)) epoch)
    a))

(defn creator
  "The ID of the world that created row `a` (nil for a world row)."
  [^objects a]
  (aget a (- (alength a) 3)))

(defn stamp
  "The owner epoch of row `a`."
  [^objects a]
  (aget a (dec (alength a))))

(defn versions [^objects a] (aget a (- (alength a) 2)))
(defn set-versions! [^objects a v] (aset a (- (alength a) 2) v))

(def ^:no-doc processed-epoch
  "Set by core: the owner epoch of the world this thread processes, or nil."
  (volatile! (fn [] nil)))

(defn check-owned!
  "Test builds (check-writes): a write to field `i` of row `r` must be by the
   world that owns it. World rows, rows written outside any world and rows
   without an owner slot are not checked."
  [^objects r i]
  (when (and (> (alength r) 2) (not= 0 (aget r 0)))   ; T-WORLD rows have no owner
    (when-let [e (@processed-epoch)]
      (let [own (aget r (dec (alength r)))]
        (when (and (some? own) (not (identical? e own)))
          (throw (ex-info "write to a row the processed world does not own"
                          {:spindel/unowned-write true :type (aget r 0) :id (aget r 1) :field i})))))))

;; Row types
(def ^:const T-WORLD 0)
(def ^:const T-SCOPE 1)
(def ^:const T-COMP 2)
(def ^:const T-TASK 3)
(def ^:const T-RUN 4)
(def ^:const T-SOURCE 5)
(def ^:const T-EDGE 6)
(def ^:const T-ACT 7)
(def ^:const T-RES 8)

(def ^:const TYPE 0)
(def ^:const ID 1)

;; World
(def ^:const W-LOCK 2)
(def ^:const W-NEXT 3)       ; long[1]: family id counter (ids >= 1, 0 = none)
(def ^:const W-ROOT 4)       ; root scope
(def ^:const W-READY 5)      ; computations to consider for dispatch
(def ^:const W-RESUME 6)     ; filled activations to resume
(def ^:const W-DRAINING 7)
(def ^:const W-RQ 8)         ; rows whose retention count reached 0 (Rule R work)
(def ^:const W-PINS 9)       ; row -> pin count
(def ^:const W-REG 10)       ; verify mode: id -> row
(def ^:const W-LOG 11)       ; verify mode: commit log
(def ^:const W-CALLBACKS 12) ; host callbacks to run after the drain
(def ^:const W-INTERN 13)    ; verify mode: opaque value -> nat
(def ^:const W-HOOK 14)      ; verify mode: (fn [w item]) after every commit
(def ^:const W-START 15)     ; task runs whose first slice is pending
(def ^:const W-CLEANUP 16)   ; [run ek]: cleanup slices of cancelled runs with finalizers
(def ^:const W-INGRESS 17)   ; H1: MPSC queue of host items (fns)
(def ^:const W-SCHEDULED 18) ; H2: AtomicBoolean, a drainer is scheduled
(def ^:const W-EXEC 19)      ; the world's executor (drainer, offload)
(def ^:const W-INLINE 20)    ; H2: host threads may process items inline
(def ^:const W-BUDGET 21)    ; H2: items + slices per inline turn
(def ^:const W-ROOTS 22)     ; observe edges and host waits (roots, §3.1) for T21
(def ^:const W-RELEASED 23)
(def ^:const W-EPOCH 24)     ; M5: this world's owner epoch (identity object)
(def ^:const W-FWD 25)       ; M5: row ID -> this world's copy (stage 1b)
(def ^:const W-ARMED 26)     ; armed resources: ordered set by ID (dormant in a fork, §8.1)
(def ^:const W-DORMANT 27)   ; a fork's inherited armed resources, activated at its first turn
(def ^:const W-SP-HANDLERS 28) ; savepoint handlers {site handler} (§8.2)
(def ^:const W-MBASE 29)       ; a mergeable fork's basis: inherited source id -> its row at the fork (L12)
(def ^:const W-MPARENT 30)     ; the world this fork merges into (its ID)
(def ^:const W-PENDING-ACT 31) ; an instantiated fork's pending activation (S3)
(def ^:const W-OWNED 32)       ; fork ownership: owner scope id -> [holders prune-threshold] (F2, E1)
(def ^:const W-HOLDER 33)      ; this fork's holder in its owner's table (E1)
(def ^:const W-UNBORN 34)      ; an instance before activate! (E4)
(def ^:const W-AFTER 35)       ; child worlds to schedule after the gate is released (E3)
(def ^:const W-PUB-WORLD 36)   ; an unborn instance's publication world, its owner at activation
(def ^:const W-STATE 37)       ; app world state: one persistent map, forked by value (M6 R1)
(def ^:const W-ATOMS 38)       ; fork-safe atoms: atom id -> [weak wrapper, value], forked by value (M6 R6)
(def ^:const W-WATCHES 39)     ; detached weak watch index, never inherited
(def ^:const W-FAMILY 40)      ; identity shared by a world and all its forks (handle lineage)
(def ^:const W-SWEEP-GEN 41)  ; last completed family atom sweep
(def ^:const W-SWEEP-PENDING 42) ; independent coalesced maintenance flag
(def ^:const W-META-CLOSED 43) ; terminal metadata cleanup completed
(def ^:const W-LINEAGE 44)    ; ([ancestor-id cut ordinal token map] ...) nearest first: rows of an ancestor
                              ; below cut are inherited; that ancestor's rows are read at its `ordinal`
                              ; (`token` keeps those versions); `map` is its copy map at the fork
(def ^:const W-TOKENS 45)     ; MVCC: the cells of this world's forks' tokens, by ascending ordinal
;; C1 world completion (c1-cancellation-joins-design.md W1-W2, R1-R2)
(def ^:const W-RUNS 46)       ; unretired runs (every task and computation run, cleanup included)
(def ^:const W-KIDS 47)       ; child-world obligations: host/kids [count released-flag], never inherited
(def ^:const W-KID-TOKEN 48)  ; host/kid-cell: the owner's token [owner-weak done-flag] and a completed flag
(def ^:const W-COMPLETE 49)   ; released, no run left, every owned child complete or collected
(def ^:const W-COMPLETE-SUBS 50) ; host terminal subscriptions [live-flag cb], never inherited
(def ^:const W-OUTSTANDING 51)   ; every resource until its acknowledgement (all phases), by ID
(def ^:const W-DISCHARGE 52)  ; a fork's inherited non-armed outstanding resources, acknowledged at its first turn
(def ^:const W-JOIN-SUBS 53)  ; C1c: host join subscriptions {task id -> list of [live-flag cb]}, never inherited
(def ^:const W-OWNED-N 54)   ; C1c stage B: counted forks per owner scope {scope id -> [scope n]}, n > 0; never inherited
(def ^:const W-NORMALIZE 55) ; C1c stage B: owner scopes a fork inherited counts on {scope id -> scope}, drained at its first turn
(def ^:const W-SEALED 56)    ; C2 (§9): a flag (SC): host admissions and host source changes refused until unseal!
(def ^:const W-ADMITTING 57) ; C2: host starts between their seal check and their enqueue (SC counter); §9 waits for 0
(def ^:const W-LOCAL 58)    ; Z#77: unretired runs of fork-local tasks {run id -> run}; a fork starts with none
(def ^:const W-RETIRE 59)   ; Z#77: the fork-local run sets inherited at the fork, retired at the first gate entry (T28)
(def ^:const W-SIZE 60)

;; Scope
(def ^:const S-PARENT 2)
(def ^:const S-KIND 3)       ; :root :run :explicit
(def ^:const S-OPEN 4)
(def ^:const S-TASKS 5)      ; running tasks owned by the scope
(def ^:const S-CHILDREN 6)   ; child scopes (explicit scopes, run scopes of owned tasks)
(def ^:const S-WORLD 7)      ; the creating world's family (detach validation)
(def ^:const S-SOURCES 8)    ; weak refs to sources owned by the scope, closed with it (T16, Z#18)
(def ^:const S-PRUNE 9)      ; prune threshold for S-SOURCES
(def ^:const S-HELD 10)      ; a run scope whose run is not retired (Z#52)
(def ^:const S-TASK 11)      ; C1c: a run scope's task, recorded when the scope is materialized
(def ^:const S-COMPLETE 12)  ; C1c: the scope row was removed (Z#18); set once
(def ^:const S-LOCAL 13)     ; Z#77: the run scope of a fork-local task or a scope below one (fixed at creation)
(def ^:const S-SIZE 14)

;; Debtor rows (computation, source, task)
(def ^:const WORLD 2)
(def ^:const OUTS 3)         ; edges with this row as debtor
(def ^:const REFS 4)         ; retention count: out-edges + basis memberships + pins (§10.10)
(def ^:const HOT 5)          ; demand: observe/wait edges + dep edges of hot creditors (Q2)
(def ^:const HANDLES 6)
(def ^:const OWNER 7)
(def ^:const VERSION 8)
(def ^:const KEY 9)          ; creation key in the creator's basis
(def ^:const AT 10)          ; creation site index in the creator's run
(def ^:const HREF 11)        ; weak reference to the row's live host handle (M3c)

;; Computation
(def ^:const C-INPUTS 12)
(def ^:const C-BODY 13)
(def ^:const C-RUN 14)
(def ^:const C-EPOCH 15)
(def ^:const C-DONE-EPOCH 16)
(def ^:const C-PENDING 17)
(def ^:const C-RANK 18)
(def ^:const C-RESULT 19)
(def ^:const C-ERR 20)
(def ^:const C-IDLE 21)
(def ^:const C-VALIDITY 22)
(def ^:const C-BASIS 23)     ; list of created rows
(def ^:const C-ADOPT 24)     ; T11 adoption basis (list) or nil
(def ^:const C-ADOPT-BASE 25); T11 adoption baselines: list of edges removed from the suffix, or nil
(def ^:const C-INS 26)       ; dep edges, ordered by at
(def ^:const C-QUEUED 27)
(def ^:const C-RESTART 28)   ; T3 changed inputs: the next run restarts from the body
(def ^:const C-FRAME 29)     ; creation keys of the creating entities and this one (§8.2 addresses)
(def ^:const C-PATH 30)      ; the creating run's path at creation, nil if empty (§8.2 P3)
(def ^:const C-BIND 31)      ; JVM: the creator's dynamic binding frame, each run's initial frame
(def ^:const C-SIZE 32)

;; Task
(def ^:const K-BODY 12)
(def ^:const K-INPUTS 13)
(def ^:const K-RUN 14)
(def ^:const K-RESULT 15)
(def ^:const K-ERR 16)
(def ^:const K-DONE 17)
(def ^:const K-FRAME 18)     ; as C-FRAME
(def ^:const K-PATH 19)      ; as C-PATH
(def ^:const K-LINK 20)      ; a realizer task: the link it realizes (C0)
(def ^:const K-SROW 21)      ; C1c: its run's scope row, once materialized (outlives the run)
(def ^:const K-COMPLETE 22)  ; C1c: done, run retired, run scope removed or never made; set once
(def ^:const K-LOCAL 23)     ; Z#77: fork-local (fixed at creation)
(def ^:const K-SIZE 24)

;; Source
(def ^:const X-KIND 12)
(def ^:const X-VALUE 13)
(def ^:const X-OPEN 14)
(def ^:const X-WAITERS 15)   ; mailbox/semaphore: FIFO of waiting wait edges
(def ^:const X-MAX 16)       ; semaphore: its maximum permit count (Z#62)
(def ^:const X-DLOG 17)      ; signal/cell: [from deltas] covering versions (from, version], or nil (§4.4)
(def ^:const X-SIZE 18)
;; Link (an async-sequence position, C0): X-VALUE is [v next-handle], nil (the
;; end) or a failure box once VERSION is 1. Reuses the mailbox/semaphore slots.
(def ^:const X-RTASK 15)     ; link: the running realizer task, or nil
(def ^:const X-REALIZE 16)   ; link: [f s frame stream-id index]; f nil for a push link

;; Resource (§1, T15-T18)
(def ^:const Z-KIND 12)      ; :offload :timer :external
(def ^:const Z-PHASE 13)     ; 0 armed, 1 fired, 2 cancelling
(def ^:const Z-RESULT 14)
(def ^:const Z-ERR 15)
(def ^:const Z-CTL 16)       ; host control: offload wrapper or ScheduledFuture
(def ^:const Z-DEADLINE 17)  ; timers: wall-clock deadline (ms), for re-arming in a fork (§8.1)
(def ^:const Z-ORIGIN 18)    ; id of the world whose controller Z-CTL is (copies elsewhere drop it, F1)
(def ^:const Z-SIZE 19)

(def ^:const Z-ARMED 1)
(def ^:const Z-FIRED 2)
(def ^:const Z-CANCELLING 3)

;; Run
(def ^:const R-WORLD 2)
(def ^:const R-OF 3)
(def ^:const R-EPOCH 4)
(def ^:const R-SCOPE 5)      ; id of the run scope (row materialized on demand)
(def ^:const R-ACT 6)        ; 0 active, 1 parked, 2 done
(def ^:const R-MODE 7)       ; 0 normal, 1 unwinding
(def ^:const R-SLICE 8)
(def ^:const R-EIDX 9)
(def ^:const R-FINS 10)
(def ^:const R-RES 11)
(def ^:const R-ACTV 12)      ; the activation the run is parked on
(def ^:const R-CURSOR 13)    ; position in the computation's INS
(def ^:const R-ORD 14)       ; creation ordinals per site
(def ^:const R-SROW 15)      ; the run scope row, once materialized
(def ^:const R-SCOPES 16)    ; open explicit scopes of the run, innermost last
(def ^:const R-PATH 17)      ; the run's path, nil if empty (§8.2 P1-P3)
(def ^:const R-BIND 18)      ; JVM: the run's dynamic binding frame between slices
(def ^:const R-INFIN 19)     ; C1 W4: depth of finally clauses executing (suspension refused)
(def ^:const R-SIZE 20)

(def ^:const ACT-ACTIVE 0)
(def ^:const ACT-PARKED 1)
(def ^:const ACT-DONE 2)

;; Edge
(def ^:const E-KIND 2)
(def ^:const E-CRED 3)       ; computation row, activation row, or host callback
(def ^:const E-DEBTOR 4)
(def ^:const E-CONT 5)       ; continuation k, or nil = restart
(def ^:const E-ERRK 6)
(def ^:const E-AT 7)
(def ^:const E-ARMED 8)
(def ^:const E-MARKED 9)
(def ^:const E-SEEN 10)      ; debtor version last consumed, or nil
(def ^:const E-BASE 11)      ; track baseline value
(def ^:const E-IDX 12)       ; position in the debtor's OUTS
(def ^:const E-ACT 13)       ; activation while an unfilled member
(def ^:const E-SLOT 14)
(def ^:const E-ORIGIN 15)    ; host edges: id of the world whose host made them (Z#45)
(def ^:const E-SIZE 16)

(def ^:const EK-DEP 0)
(def ^:const EK-WAIT 1)
(def ^:const EK-OBSERVE 2)
(def ^:const EK-SAVEPOINT 3)

;; Activation
(def ^:const A-RUN 2)
(def ^:const A-MODE 3)
(def ^:const A-SLOTS 4)      ; object array of filled results ([v err?] pairs)
(def ^:const A-REMAINING 5)
(def ^:const A-R 6)
(def ^:const A-E 7)
(def ^:const A-INLINE 8)     ; the awaiting frame is still on the host stack (I10)
(def ^:const A-MEMBERS 9)    ; object array: the unfilled member edge per slot (Z#7), nil once filled
(def ^:const A-WINNER 10)    ; `any`: the slot that resumed it
(def ^:const A-RESULT 11)    ; the delivery, once resumed at the fill (T6/T9)
(def ^:const A-RESUMED 12)
(def ^:const A-SIZE 13)

(def ^:const SRC-SIGNAL 0)
(def ^:const SRC-CELL 1)
(def ^:const SRC-DEFERRED 2)
(def ^:const SRC-MAILBOX 3)
(def ^:const SRC-SEMAPHORE 4)
(def ^:const SRC-LINK 5)     ; once-cell of an async sequence (C0)
(def ^:const SRC-STREAM 6)   ; push-stream producer: X-VALUE is its tail link (C0)

(def kind-names [:signal :cell :deferred :mailbox :semaphore :link :stream])
