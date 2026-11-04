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
     (defmacro alist [] (if (cljs? &env) `(cljs.core/array) `(java.util.ArrayList.)))
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
(def ^:const W-SIZE 16)

;; Scope
(def ^:const S-PARENT 2)
(def ^:const S-KIND 3)       ; :root :run :explicit
(def ^:const S-OPEN 4)
(def ^:const S-TASKS 5)      ; running tasks owned by the scope
(def ^:const S-CHILDREN 6)   ; child scopes (explicit scopes, run scopes of owned tasks)
(def ^:const S-WORLD 7)
(def ^:const S-SIZE 8)

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

;; Computation
(def ^:const C-INPUTS 11)
(def ^:const C-BODY 12)
(def ^:const C-RUN 13)
(def ^:const C-EPOCH 14)
(def ^:const C-DONE-EPOCH 15)
(def ^:const C-PENDING 16)
(def ^:const C-RANK 17)
(def ^:const C-RESULT 18)
(def ^:const C-ERR 19)
(def ^:const C-IDLE 20)
(def ^:const C-VALIDITY 21)
(def ^:const C-BASIS 22)     ; list of created rows
(def ^:const C-ADOPT 23)     ; T11 adoption basis (list) or nil
(def ^:const C-ADOPT-BASE 24); T11 adoption baselines: list of edges removed from the suffix, or nil
(def ^:const C-INS 25)       ; dep edges, ordered by at
(def ^:const C-QUEUED 26)
(def ^:const C-RESTART 27)   ; T3 changed inputs: the next run restarts from the body
(def ^:const C-SIZE 28)

;; Task
(def ^:const K-BODY 11)
(def ^:const K-INPUTS 12)
(def ^:const K-RUN 13)
(def ^:const K-RESULT 14)
(def ^:const K-ERR 15)
(def ^:const K-DONE 16)
(def ^:const K-SIZE 17)

;; Source
(def ^:const X-KIND 11)
(def ^:const X-VALUE 12)
(def ^:const X-OPEN 13)
(def ^:const X-SIZE 14)

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
(def ^:const R-SIZE 16)

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
(def ^:const E-SIZE 15)

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
(def ^:const A-WAITS 9)      ; wait members (edges with this activation as creditor)
(def ^:const A-SIZE 10)

(def ^:const SRC-SIGNAL 0)
(def ^:const SRC-CELL 1)
(def ^:const SRC-DEFERRED 2)
(def ^:const SRC-MAILBOX 3)
(def ^:const SRC-SEMAPHORE 4)
