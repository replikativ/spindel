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
     (defmacro s! [row i v]
       (let [s (with-meta (gensym "row") {:tag 'objects})]
         (if (cljs? &env)
           `(let [~s ~row] (aset ~s ~i ~v))
           `(let [~s ~row] (clojure.lang.RT/aset ~s (int ~i) (clojure.lang.RT/box ~v))))))
     (defmacro gl [row i] `(long (g ~row ~i)))
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
(defn new-row
  "A row of `size` fields plus its owner-epoch slot."
  ^objects [epoch size]
  (let [a (object-array (inc (long size)))]
    (aset a (long size) epoch)
    a))

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
(def ^:const W-SAVEPOINTS 29)  ; pending savepoint activations, ordered set by ID
(def ^:const W-SP-DORMANT 30)  ; a fork's inherited pending savepoints (fail err ::forked)
(def ^:const W-PENDING-ACT 31) ; an instantiated fork's pending activation (S3)
(def ^:const W-ACKS 32)        ; resources joined at cancel, acknowledged as their own item (Z#55)
(def ^:const W-OWNED 33)       ; fork ownership: owner scope id -> [holders prune-threshold] (F2, E1)
(def ^:const W-HOLDER 34)      ; this fork's holder in its owner's table (E1)
(def ^:const W-UNBORN 35)      ; an instance before activate! (E4)
(def ^:const W-AFTER 36)       ; child worlds to schedule after the gate is released (E3)
(def ^:const W-PUB-WORLD 37)   ; an unborn instance's publication world, its owner at activation
(def ^:const W-SIZE 38)

;; Scope
(def ^:const S-PARENT 2)
(def ^:const S-KIND 3)       ; :root :run :explicit
(def ^:const S-OPEN 4)
(def ^:const S-TASKS 5)      ; running tasks owned by the scope
(def ^:const S-CHILDREN 6)   ; child scopes (explicit scopes, run scopes of owned tasks)
(def ^:const S-WORLD 7)
(def ^:const S-SOURCES 8)    ; weak refs to sources owned by the scope, closed with it (T16, Z#18)
(def ^:const S-PRUNE 9)      ; prune threshold for S-SOURCES
(def ^:const S-HELD 10)      ; a run scope whose run is not retired (Z#52)
(def ^:const S-SIZE 11)

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
(def ^:const C-SIZE 29)

;; Task
(def ^:const K-BODY 12)
(def ^:const K-INPUTS 13)
(def ^:const K-RUN 14)
(def ^:const K-RESULT 15)
(def ^:const K-ERR 16)
(def ^:const K-DONE 17)
(def ^:const K-SIZE 18)

;; Source
(def ^:const X-KIND 12)
(def ^:const X-VALUE 13)
(def ^:const X-OPEN 14)
(def ^:const X-WAITERS 15)   ; mailbox/semaphore: FIFO of waiting wait edges
(def ^:const X-SIZE 16)

;; Resource (§1, T15-T18)
(def ^:const Z-KIND 12)      ; :offload :timer
(def ^:const Z-PHASE 13)     ; 0 armed, 1 fired, 2 cancelling
(def ^:const Z-RESULT 14)
(def ^:const Z-ERR 15)
(def ^:const Z-CTL 16)       ; host control: offload wrapper or ScheduledFuture
(def ^:const Z-DEADLINE 17)  ; timers: wall-clock deadline (ms), for re-arming in a fork (§8.1)
(def ^:const Z-SIZE 18)

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
(def ^:const R-SIZE 17)

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
