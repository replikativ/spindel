(ns org.replikativ.spindel.engine.impl.owned
  "Owned-object CPS engine under construction. Canonical maps are diagnostic output,
  never the live representation. Supports the local reactive lifetime slice."
  (:refer-clojure :exclude [await assoc! dissoc! pop!])
  #?(:cljs (:require-macros [org.replikativ.spindel.engine.impl.owned :refer [a put locked each! each-copy! fields! with-activation runtime-field]]))
  (:require [is.simm.partial-cps.async :as cps]
            [is.simm.partial-cps.runtime :as cps-runtime]
            #?(:clj [is.simm.partial-cps.ioc :as ioc])
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.engine.cell-handles :as cell-handles]
            [org.replikativ.spindel.engine.timer-transport :as timer-transport]
            [org.replikativ.spindel.engine.fault :as fault]
            [org.replikativ.spindel.engine.lifecycle :as lifecycle]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.incremental.deltaable :as delta]))

#?(:clj (defonce ^:private activation-local (ThreadLocal.))
   :cljs (def ^:private active-frame nil))
(defn- current-activation []
  #?(:clj (.get ^ThreadLocal activation-local) :cljs active-frame))
#?(:clj
   (defmacro with-activation [frame & body]
     (if (:ns &env)
       `(let [previous# active-frame]
          (set! active-frame ~frame)
          (try ~@body (finally (set! active-frame previous#))))
       `(let [previous# (.get ^ThreadLocal activation-local)]
          (.set ^ThreadLocal activation-local ~frame)
          (try ~@body (finally (.set ^ThreadLocal activation-local previous#)))))))
#?(:clj
   (do
     (defmacro a [xs i]
       (if (:ns &env)
         `(cljs.core/aget ~xs ~i)
         (let [read `(let [^"[Ljava.lang.Object;" array# ~xs] (aget array# (int ~i)))]
           (if-let [tag (:tag (meta &form))]
             (let [value (with-meta (gensym "value") {:tag tag})]
               `(let [~value ~read] ~value))
             read))))
     (defmacro put [xs i value]
       (if (:ns &env) `(cljs.core/aset ~xs ~i ~value) `(let [^"[Ljava.lang.Object;" array# ~xs] (aset array# (int ~i) (clojure.lang.RT/box ~value)))))))
(defn- slots [n] #?(:clj (object-array n) :cljs (make-array n)))
#?(:cljs (deftype IDMap [buckets]))
#?(:cljs
   (deftype ValuesView [m]
     ;; Borrowed views stay internal; snapshots realize values under the gate.
     ISeqable
     (-seq [_]
       (when (pos? (.-size m)) (array-seq (js/Array.from (.values m)))))))
#?(:cljs
   (deftype OwnedQueue [^:mutable buffer ^:mutable head ^:mutable length]
     Object
     (grow [_]
       (let [old buffer capacity (.-length old) next (doto (make-array (* 2 capacity)) (.fill nil))]
         (dotimes [i length] (aset next i (aget old (bit-and (+ head i) (dec capacity)))))
         (set! buffer next) (set! head 0)))
     (add [this value]
       (when (= length (.-length buffer)) (.grow this))
       (aset buffer (bit-and (+ head length) (dec (.-length buffer))) value)
       (set! length (inc length))
       this)
     (resetEmpty [_]
       (set! head 0)
       (when (> (.-length buffer) 256)
         (set! buffer (doto (make-array 16) (.fill nil)))))
     (peek [_]
       (when (pos? length) (aget buffer head)))
     (poll [this]
       (when (pos? length)
         (let [value (aget buffer head)]
           (aset buffer head nil)
           (set! length (dec length))
           (if (zero? length) (.resetEmpty this)
               (set! head (bit-and (inc head) (dec (.-length buffer)))))
           value)))
     (removeAt [this index]
       (let [mask (dec (.-length buffer))]
         (loop [i index]
           (when (< i (dec length))
             (aset buffer (bit-and (+ head i) mask) (aget buffer (bit-and (+ head i 1) mask)))
             (recur (inc i))))
         (aset buffer (bit-and (+ head length -1) mask) nil)
         (set! length (dec length))
         (when (zero? length) (.resetEmpty this))))
     (remove [this value]
       (loop [i 0]
         (if (= i length) false
             (if (identical? value (aget buffer (bit-and (+ head i) (dec (.-length buffer)))))
               (do (.removeAt this i) true)
               (recur (inc i))))))
     (removeWhere [this pred]
       (let [n length mask (dec (.-length buffer))]
         (loop [read 0 write 0]
           (if (< read n)
             (let [value (aget buffer (bit-and (+ head read) mask))]
               (if (pred value) (recur (inc read) write)
                   (do (aset buffer (bit-and (+ head write) mask) value)
                       (recur (inc read) (inc write)))))
             (do (dotimes [i (- n write)] (aset buffer (bit-and (+ head write i) mask) nil))
                 (set! length write)
                 (when (zero? length) (.resetEmpty this)))))))
     (clear [this]
       (.fill buffer nil) (set! length 0) (.resetEmpty this))
     (toArray [_]
       (let [result (make-array length) mask (dec (.-length buffer))]
         (dotimes [i length] (aset result i (aget buffer (bit-and (+ head i) mask))))
         result))
     (forEach [_ visit]
       (dotimes [i length] (visit (aget buffer (bit-and (+ head i) (dec (.-length buffer)))))))
     (some [_ pred]
       (loop [i 0]
         (if (= i length) false
             (if (pred (aget buffer (bit-and (+ head i) (dec (.-length buffer))))) true
                 (recur (inc i))))))
     (capacity [_] (.-length buffer))
     (staleReferences [_]
       (let [mask (dec (.-length buffer))]
         (loop [i 0 n 0]
           (if (= i (.-length buffer)) n
               (recur (inc i) (if (and (>= (bit-and (- i head) mask) length)
                                       (some? (aget buffer i))) (inc n) n))))))))
(defn- empty-native? [xs]
  #?(:clj (.isEmpty ^java.util.Collection xs)
     :cljs (cond (instance? ValuesView xs) (zero? (.-size (.-m xs)))
                 (instance? OwnedQueue xs) (zero? (.-length xs))
                 (array? xs) (zero? (.-length xs))
                 :else (zero? (.-size xs)))))
(defn- dict []
  #?(:clj (java.util.HashMap.)
     :cljs (let [m (js/Map.)]
             (set! (.-spindelValues m) (ValuesView. m))
             m)))
(defn- id-dict [] #?(:clj (dict) :cljs (IDMap. (js/Map.))))
(defn- find! [m k]
  #?(:clj (.get ^java.util.Map m k)
     :cljs (if (instance? IDMap m)
             (when-let [bucket (.get (.-buckets m) (hash k))]
               (loop [i 0]
                 (when (< i (.-length bucket))
                   (if (= k (aget bucket i)) (aget bucket (inc i)) (recur (+ i 2))))))
             (.get m k))))
(defn- assoc! [m k v]
  #?(:clj (.put ^java.util.Map m k v)
     :cljs (if (instance? IDMap m)
             (let [h (hash k) buckets (.-buckets m)]
               (if-let [bucket (.get buckets h)]
                 (loop [i 0]
                   (if (= i (.-length bucket)) (.push bucket k v)
                       (if (= k (aget bucket i)) (aset bucket (inc i) v) (recur (+ i 2)))))
                 (.set buckets h (array k v))))
             (.set m k v))) v)
(defn- dissoc! [m k]
  #?(:clj (.remove ^java.util.Map m k)
     :cljs (if (instance? IDMap m)
             (let [h (hash k) buckets (.-buckets m)]
               (when-let [bucket (.get buckets h)]
                 (loop [i 0]
                   (when (< i (.-length bucket))
                     (if (= k (aget bucket i))
                       (do (.splice bucket i 2)
                           (when (zero? (.-length bucket)) (.delete buckets h)))
                       (recur (+ i 2)))))))
             (.delete m k))))
#?(:cljs
   (defn- same-set-value? [x y]
     (or (identical? x y)
         (and (number? x) (number? y) (js/isNaN x) (js/isNaN y)))))

#?(:cljs
   (deftype InlineSet [^:mutable one ^:mutable two ^:mutable three ^:mutable size ^:mutable overflow]
     ;; Internal membership storage, not a public collection. Traversal borrows
     ;; a stable membership; destructive loops must use each-copy!, as on JVM.
     Object
     (has [_ value]
       (if overflow (.has overflow value)
           (boolean (or (and (> size 0) (same-set-value? value one))
                        (and (> size 1) (same-set-value? value two))
                        (and (> size 2) (same-set-value? value three))))))
     (add [this value]
       (if overflow
         (do (.add overflow value) (set! size (.-size overflow)))
         (when-not (.has this value)
           (let [value (if (identical? value 0) 0 value)]
             (case size
               0 (set! one value)
               1 (set! two value)
               2 (set! three value)
               3 (do (set! overflow (js/Set. (array one two three value)))
                     (set! one nil) (set! two nil) (set! three nil))))
           (set! size (inc size))))
       this)
     (delete [_ value]
       (if overflow
         (let [removed? (.delete overflow value)]
           (set! size (.-size overflow))
           (when (zero? size) (set! overflow nil))
           removed?)
         (cond
           (and (> size 0) (same-set-value? value one))
           (do (set! one two) (set! two three) (set! three nil) (set! size (dec size)) true)
           (and (> size 1) (same-set-value? value two))
           (do (set! two three) (set! three nil) (set! size (dec size)) true)
           (and (> size 2) (same-set-value? value three))
           (do (set! three nil) (set! size 2) true)
           :else false)))
     (clear [_]
       (set! one nil) (set! two nil) (set! three nil)
       (set! size 0) (set! overflow nil))
     (forEach [_ visit]
       (if overflow (.forEach overflow visit)
           (do (when (> size 0) (visit one))
               (when (> size 1) (visit two))
               (when (> size 2) (visit three)))))
     (copyInto [_ target]
       (if overflow
         (let [i (volatile! 0)]
           (.forEach overflow (fn [value] (aset target @i value) (vswap! i inc))))
         (do (when (> size 0) (aset target 0 one))
             (when (> size 1) (aset target 1 two))
             (when (> size 2) (aset target 2 three))))
       size)
     (some [_ pred]
       (if overflow
         (let [it (.values overflow)]
           (loop []
             (let [entry (.next it)]
               (if (.-done entry) false
                   (if (pred (.-value entry)) true (recur))))))
         (boolean (or (and (> size 0) (pred one))
                      (and (> size 1) (pred two))
                      (and (> size 2) (pred three))))))
     (toArray [_]
       (if overflow (js/Array.from overflow)
           (case size 0 (array) 1 (array one) 2 (array one two) 3 (array one two three))))))

(defn- members [] #?(:clj (java.util.HashSet.) :cljs (InlineSet. nil nil nil 0 nil)))
(def ^:private empty-members #?(:clj (java.util.Collections/emptySet) :cljs (js/Set.)))
(defn- clear-members! [s]
  (when-not (empty-native? s)
    #?(:clj (.clear ^java.util.Set s) :cljs (.clear s))))
(defn- add! [s x] #?(:clj (.add ^java.util.Set s x) :cljs (.add s x)))
(defn- remove! [s x] #?(:clj (.remove ^java.util.Set s x) :cljs (.delete s x)))
(defn- has? [s x] #?(:clj (.contains ^java.util.Set s x) :cljs (.has s x)))
(defn- items [s]
  #?(:clj (seq s)
     :cljs (if (instance? ValuesView s) (seq s)
               (array-seq (if (or (instance? InlineSet s) (instance? OwnedQueue s)) (.toArray s) (js/Array.from s))))))
(defn- values [m]
  #?(:clj (.values ^java.util.Map m)
     :cljs (if (instance? IDMap m)
             (let [result (array)]
               (.forEach (.-buckets m)
                         (fn [bucket] (loop [i 1]
                                        (when (< i (.-length bucket))
                                          (.push result (aget bucket i)) (recur (+ i 2))))))
               result)
             (.-spindelValues m))))
(defn- count! [s] #?(:clj (.size ^java.util.Collection s) :cljs (.-size s)))
(defn- queue [] #?(:clj (java.util.ArrayDeque.) :cljs (OwnedQueue. (doto (make-array 16) (.fill nil)) 0 0)))
(defn- push! [q x] #?(:clj (.addLast ^java.util.ArrayDeque q x) :cljs (.add q x)))
(defn- pop! [q] #?(:clj (.pollFirst ^java.util.ArrayDeque q) :cljs (.poll q)))
(defn- queue-front [q] #?(:clj (.peekFirst ^java.util.ArrayDeque q) :cljs (.peek q)))
(defn- queued? [q] #?(:clj (not (.isEmpty ^java.util.ArrayDeque q)) :cljs (pos? (.-length q))))

(def ^:private empty-array #?(:clj (object-array 0) :cljs (array)))
(defn- copy-items [xs]
  #?(:clj (.toArray ^java.util.Collection xs ^objects empty-array)
     :cljs (cond (empty-native? xs) empty-array
                 (or (instance? InlineSet xs) (instance? OwnedQueue xs)) (.toArray xs)
                 :else (js/Array.from (if (instance? ValuesView xs) (.values (.-m xs)) xs)))))
(defn- any! [xs pred]
  (when-not (empty-native? xs)
    #?(:clj (let [it (.iterator ^java.lang.Iterable xs)]
              (loop [] (when (.hasNext it)
                         (let [x (.next it)] (if (pred x) true (recur))))))
       :cljs (if (or (instance? InlineSet xs) (instance? OwnedQueue xs)) (.some xs pred)
                 (let [it (if (instance? ValuesView xs) (.values (.-m xs))
                              (js* "~{}[Symbol.iterator]()" xs))]
                   (loop [] (let [entry (.next it)]
                              (when-not (.-done entry)
                                (if (pred (.-value entry)) true (recur))))))))))

#?(:clj
   (do
     (defmacro each! [[x xs] & body]
       (if (:ns &env)
         `(let [coll# ~xs]
            (when-not (empty-native? coll#)
              (.forEach (if (instance? ValuesView coll#) (.-m coll#) coll#)
                        (fn [~x] ~@body))))
         `(let [^java.util.Collection coll# ~xs]
            (when-not (.isEmpty coll#)
              (let [^java.util.Iterator it# (.iterator coll#)]
                (while (.hasNext it#) (let [~x (.next it#)] ~@body)))))))
     (defmacro fields! [[field fields] & body]
       `(do ~@(map (fn [value] `(let [~field ~value] ~@body)) fields)))
     (defmacro each-copy! [[x xs] & body]
       `(let [items# (copy-items ~xs)]
          (dotimes [i# (alength ^"[Ljava.lang.Object;" items#)]
            (let [~x (a items# i#)] ~@body))))))

;; Fixed layouts; graph links point to engine-owned objects in this local slice.
(def ^:const n-id 0) (def ^:const n-kind 1) (def ^:const n-owner 2)
(def ^:const n-creator 3) (def ^:const n-complete 4) (def ^:const n-kept 5)
(def ^:const n-value 6) (def ^:const n-tokens 7) (def ^:const n-order 8)
(def ^:const n-dirty 9) (def ^:const n-runs 10) (def ^:const n-dependents 11)
(def ^:const n-generation 12) (def ^:const n-body 13) (def ^:const n-rank 14)
(def ^:const n-ready 15) (def ^:const n-resume 16) (def ^:const n-work 17) (def ^:const n-current 18) (def ^:const n-pending-generation 19)
(def ^:const n-runtime 20) (def ^:const n-origin 21) (def ^:const n-source-world 22) (def ^:const n-created-by 23) (def ^:const n-creator-refs 24) (def ^:const n-creator-source 25)
(def ^:const n-source-event 26)
(def ^:const n-links 27) (def ^:const n-link-buffer 28) (def ^:const n-supporters 29)
(def ^:const n-graph-dirty 30) (def ^:const n-external-root 31)
(def ^:const n-descriptor 32)
(def ^:const n-cancelled 33)
(def ^:const n-public-signal 34)
(def ^:const n-deferred 35) (def ^:const n-mailbox 36)
(def ^:const r-node 0) (def ^:const r-gen 1) (def ^:const r-owner 2)
(def ^:const r-pred 3) (def ^:const r-status 4) (def ^:const r-created 5)
(def ^:const r-spawned 6) (def ^:const r-seq 7) (def ^:const r-obs 8)
(def ^:const r-owned 9) (def ^:const r-backlinks 10) (def ^:const r-childruns 11) (def ^:const r-physical 12) (def ^:const r-anchor 13) (def ^:const r-origin 14) (def ^:const r-source-world 15) (def ^:const r-wide 16) (def ^:const r-reactives 17) (def ^:const r-ancestors 18) (def ^:const r-validation-lost 19)
(def ^:const r-entered 20) (def ^:const r-finalization-seq 21)
(def ^:const r-exit 22) (def ^:const r-cancel-cont 23)
(def ^:const r-address 24) (def ^:const r-timers 25)

;; Protected tickets contain identity, continuations and opaque retained payloads.
;; They never retain a retired logical run or its ownership graph.
(def ^:const x-id 0) (def ^:const x-anchor 1) (def ^:const x-kind 2)
(def ^:const x-phase 3) (def ^:const x-seq 4) (def ^:const x-resolve 5)
(def ^:const x-reject 6) (def ^:const x-value 7) (def ^:const x-failed 8)
(def ^:const x-cells 9) (def ^:const x-run 10) (def ^:const x-physical 11)
(def ^:const x-queued 12) (def ^:const x-delivered 13)
(def ^:const x-address 15)
(def ^:const x-cancel-value 16)

(def ^:const x-operation 17)
;; A protected operation owns callback registrations, separately from its
;; enclosing ticket's parent continuation and physical slice.
(def ^:const p-id 0) (def ^:const p-ticket 1) (def ^:const p-parent 2)
(def ^:const p-state 3) (def ^:const p-registrations 4) (def ^:const p-next 5)
(def ^:const p-physical 6) (def ^:const p-queued 7) (def ^:const p-frame-next 8)
(def ^:const p-terminal 9) (def ^:const p-frames 10)
(def ^:const g-id 0) (def ^:const g-operation 1) (def ^:const g-allocation 2)
(def ^:const g-control 3) (def ^:const g-key 4) (def ^:const g-state 5)
(def ^:const g-resolve 6) (def ^:const g-reject 7) (def ^:const g-value 8)
(def ^:const g-entered 9) (def ^:const g-mailbox 10)

(def ^:const m-messages 0) (def ^:const m-consumers 1) (def ^:const m-pending 2)
(def ^:const m-reservations 3) (def ^:const m-protected 4) (def ^:const m-physical 5)
(def ^:const b-id 0) (def ^:const b-kind 1) (def ^:const b-ob 2) (def ^:const b-registration 3)
(def ^:const b-state 4) (def ^:const b-message 5) (def ^:const b-resolve 6) (def ^:const b-reject 7)
(def ^:const b-anchor 8) (def ^:const b-owner 9) (def ^:const b-control 10) (def ^:const b-allocation 11)
(def ^:const b-key 12) (def ^:const b-frame 13) (def ^:const b-node 14) (def ^:const b-receipt 15)
(def ^:const b-context 16) (def ^:const b-run 17)
(def ^:const b-error 18) (def ^:const b-error-receipt 19)

(defn- active-mailbox-callback []
  (when-let [frame (current-activation)]
    (when (> (alength ^objects frame) 12) (a frame 12))))

(defn- active-operation []
  (when-let [frame (current-activation)]
    (when (> (alength ^objects frame) 10) (a frame 10))))
(defn- operation-retired? [operation]
  (= :cps-exit (a (a operation p-ticket) x-kind)))

(def ^:const o-id 0) (def ^:const o-kind 1) (def ^:const o-debtor 2)
(def ^:const o-run 3) (def ^:const o-standing 4) (def ^:const o-resolve 5)
(def ^:const o-reject 6) (def ^:const o-order 7) (def ^:const o-slot 8)
;; Slot 9 is a callback for host creditors and a delivery error bit for run
;; creditors. These roles are disjoint; ordinary payloads never encode errors.
(def ^:const o-success 9) (def ^:const o-delivery-error 9) (def ^:const o-failure 10) (def ^:const o-last 11)
(def ^:const o-live 12) (def ^:const o-value 13) (def ^:const o-host 14)
(def ^:const o-address 19)
(def ^:const o-body 20)
(def ^:const o-signal-generation 21) (def ^:const o-mailbox 22) (def ^:const o-timer 23)
(def ^:const o-origin 15) (def ^:const o-source-world 16) (def ^:const o-creditor-generation 17) (def ^:const o-creditor-node 18)
(def ^:const t-id 0) (def ^:const t-spin 1) (def ^:const t-reachable 2)
(def ^:const t-touched 3) (def ^:const t-dropped 4) (def ^:const t-family 6)

(defrecord Handle [id token body])
(defrecord Source [id family allocation])
(defrecord DeferredRef [id family anchor])
(defrecord MailboxRef [id family anchor])
(defrecord Ticket [id])
(defrecord Delivery [family world obligation])
(deftype RootOwner [id]
  ;; Runtime identity is opaque even when independent worlds have the same
  ;; symbolic model coordinate. The sole field is data, never the runtime.
  #?(:clj clojure.lang.ILookup :cljs ILookup)
  (#?(:clj valAt :cljs -lookup) [_ key]
    (when (= :id key) id))
  (#?(:clj valAt :cljs -lookup) [_ key not-found]
    (if (= :id key) id not-found)))
(deftype ^:private ScopeCapability [world id])
(deftype ^:private ScopeOwner [data])
(deftype ^:private CapturedOwner [owner role world spin])
(def ^:const s-id 0) (def ^:const s-cap 1) (def ^:const s-parent 2)
(def ^:const s-kind 3) (def ^:const s-order 4) (def ^:const s-open 6)
(def ^:const s-owned 9) (def ^:const s-runs 11)
(def ^:const s-origin 14) (def ^:const s-source-world 15)

(defrecord Failure [error])

(defn- diagnostic-value [value failed?]
  (if failed? (->Failure value) value))
 ;; Timer lifetime is separate from its ended logical wait and opaque handle.
(def ^:const z-id 0) (def ^:const z-run 1) (def ^:const z-ob 2)
(def ^:const z-order 3) (def ^:const z-delay 4) (def ^:const z-value 5)
(def ^:const z-phase 6) (def ^:const z-install 7) (def ^:const z-handle-state 8)
(def ^:const z-handle 9) (def ^:const z-frames 10)
(deftype ^:private NativeReleaseReceipt [owner token])
(deftype ^:private NativeWorldCapability [family id token])
(deftype ^:private NativeDiscardReceipt [target token])
(defrecord ^:private CustodyHolder [root world kind id])
(defonce ^:private pending-releases (atom {}))
(defrecord RuntimeFamily [gate worlds host-tokens cell-gc])
;; Borrowed only while an admitted custody transaction is on the stack.
(def ^:private ^:dynamic *custody-frame* nil)
(def ^:private ^:dynamic *world-release-cancellation* nil)
(declare read-application-state swap-application-state! cas-application-state!
         allocate-cell! cell-present? read-cell-value read-cell-meta read-cell-watches
         swap-cell! cas-cell! add-cell-watch! remove-cell-watch! collect-home-cell! retry-cell-gc! next-trace-address!
         register-computation! invoke-computation! cancel-computation! computation-result deref-computation!
         await-public-timer! timer-revoke! timer-profile-view prune-timer-queue! same-cell-world?
         request-world-release! observe-world-release! refresh-release! world-open! release-view lifecycle-await!
         create-public-deferred! claim-public-deferred! deliver-public-deferred! read-public-deferred invoke-public-deferred!
         operation-deliver! protect-deferred! start-protected-operation! invoke-operation-ready! operation-terminal! operation-check!
         create-public-mailbox! post-public-mailbox! take-public-mailbox-now! invoke-public-mailbox! invoke-public-mailbox-next!
         await-public-mailbox! mailbox-view! mailbox-metadata mailbox-detach! mailbox-enter! mailbox-return!
         queue-mailbox-rejection! invoke-mailbox-rejection! refresh-mailbox-owner! process-mailbox-post! mailbox-callback-check! protect-mailbox! mailbox-owner-anchor
         assign-deferred! await-public-deferred! deferred-view! deferred-metadata end-deferred-protection! release-ticket-cells!
         public-signal-view! register-public-signal! public-signal-value public-signal-state swap-public-signal! cas-public-signal!
         clear-public-signal-deltas! public-signal-watches edit-public-signal-watch! publish-public-signals! track-public-signal!
         await-public-computation! await-public-finalization! prepare-computation! canonical-runtime public-slice! invoke-public-computation! weak-descriptor
         root-execution-owner current-execution-owner open-execution-scope! bindable-execution-owner
         capture-execution-owner restore-execution-owner
         close-execution-scope! execution-owner-joined? selected-owner close-owner! check-scope-close! owner-capability
         fork-owned-world! transfer-owned-world! discard-owned-world! observe-owned-world-disposal!
         custody-state! custody-state custody-publish! custody-project custody-cap-view custody-holder-view
         custody-claim-owner! custody-adopt! custody-dispatch! refresh-custody! refresh-custody-releases! custody-debts? custody-world-phase
         custody-publication-owner custody-release-preflight! custody-event? custody-event-view custody-live? custody-release-ready?
         custody-data-world? custody-audit-family custody-release-data! custody-targets-view custody-shape! custody-holder custody-reachable-roots custody-owner-holds? custody-order custody-disposal-preflight! custody-resource-ingress! custody-protected-roots custody-automatic-holder?)
;; Every public/scoped view shares one revocable world arena. Only value/identity
;; fields live on the facade; borrowed family services never become view aliases.
(defrecord ^:private ArenaState [nodes deliveries events hosts work ready draining counters audit tokens
                                 serial thread family parent tickets lineage gc operations posts home liveness
                                 extension-state finalization managed-cells trace-address timers lifecycle execution-scopes])
(defrecord OwnedRuntime [gate world root family-id owner-root arena-cell]
  rtp/PExecutionScopes
  (root-execution-owner [this] (root-execution-owner this))
  (current-execution-owner [this] (current-execution-owner this))
  (open-execution-scope! [this kind parent] (open-execution-scope! this kind parent))
  (bindable-execution-owner [this owner] (bindable-execution-owner this owner))
  (capture-execution-owner [this owner] (capture-execution-owner this owner))
  (restore-execution-owner [this captured current] (restore-execution-owner this captured current))
  (close-execution-scope! [this scope] (close-execution-scope! this scope))
  (execution-owner-joined? [this owner] (execution-owner-joined? this owner))
  rtp/PWorldCustody
  (fork-owned-world! [this options] (fork-owned-world! this options))
  (transfer-owned-world! [this bearer caller destination acceptor options]
    (transfer-owned-world! this bearer caller destination acceptor options))
  (discard-owned-world! [this bearer caller options] (discard-owned-world! this bearer caller options))
  (observe-owned-world-disposal! [this receipt resolve reject]
    (observe-owned-world-disposal! this receipt resolve reject))
  rtp/PWorldLifecycle
  (request-world-release! [this reason] (request-world-release! this reason))
  (observe-world-release! [this receipt resolve reject] (observe-world-release! this receipt resolve reject))
  rtp/PTimers
  (await-public-timer! [this delay-ms value resolve reject]
    (await-public-timer! this delay-ms value resolve reject))
  rtp/PMailboxSynchronization
  (create-public-mailbox! [this id] (create-public-mailbox! this id))
  (post-public-mailbox! [this target value]
    (try (post-public-mailbox! this target value)
         (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))
  (take-public-mailbox-now! [this target consumer-id]
    (try (take-public-mailbox-now! this target consumer-id)
         (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))
  (invoke-public-mailbox! [this target resolve reject]
    (try (invoke-public-mailbox! this target resolve reject)
         (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))
  (invoke-public-mailbox-next! [this target resolve reject]
    (try (invoke-public-mailbox-next! this target resolve reject)
         (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))
  rtp/PSynchronization
  (create-public-deferred! [this id] (create-public-deferred! this id))
  (claim-public-deferred! [this ref value]
    (try (claim-public-deferred! this ref value)
         (finally #?(:clj (java.lang.ref.Reference/reachabilityFence ref) :cljs nil))))
  (deliver-public-deferred! [this ref value]
    (try (deliver-public-deferred! this ref value)
         (finally #?(:clj (java.lang.ref.Reference/reachabilityFence ref) :cljs nil))))
  (read-public-deferred [this ref]
    (try (read-public-deferred this ref)
         (finally #?(:clj (java.lang.ref.Reference/reachabilityFence ref) :cljs nil))))
  (invoke-public-deferred! [this ref resolve reject]
    (try (invoke-public-deferred! this ref resolve reject)
         (finally #?(:clj (java.lang.ref.Reference/reachabilityFence ref) :cljs nil))))
  rtp/PSignals
  (register-public-signal! [this ref] (register-public-signal! this ref))
  (public-signal-value [this ref] (public-signal-value this ref))
  (public-signal-state [this ref] (public-signal-state this ref))
  (swap-public-signal! [this ref f args publish? committed observe-change?]
    (swap-public-signal! this ref f args publish? committed observe-change?))
  (cas-public-signal! [this ref old-value new-value publish?]
    (cas-public-signal! this ref old-value new-value publish?))
  (clear-public-signal-deltas! [this ref] (clear-public-signal-deltas! this ref))
  (public-signal-watches [this ref] (public-signal-watches this ref))
  (add-public-signal-watch! [this ref key f] (edit-public-signal-watch! this ref key f true))
  (remove-public-signal-watch! [this ref key] (edit-public-signal-watch! this ref key nil false))
  (publish-public-signals! [this ids] (publish-public-signals! this ids))
  rtp/PSignalTracking
  (track-public-signal! [this ref caller-id source-loc resolve reject]
    (track-public-signal! this ref caller-id source-loc resolve reject))
  rtp/PComputations
  (register-computation! [this target id body] (register-computation! this target id body))
  (invoke-computation! [this target id body resolve reject mode]
    (invoke-computation! this target id body resolve reject mode))
  (cancel-computation! [this target id body reason] (cancel-computation! this target id body reason))
  (computation-result [this target id] (computation-result this target id))
  (deref-computation! [this target id body timeout-ms timeout-val]
    (deref-computation! this target id body timeout-ms timeout-val))
  rtp/PComputationAwait
  (await-computation! [this target id body caller-id source-loc resolve reject]
    (try (await-public-computation! this target id body caller-id source-loc resolve reject)
         (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))
  (await-computation-finalization! [this operation caller-id source-loc resolve reject]
    (await-public-finalization! this operation caller-id source-loc resolve reject))
  rtp/PTraceAddressing
  (next-trace-address! [this prefix source-loc] (next-trace-address! this prefix source-loc))
  rtp/PWorldIdentity
  (world-identity [_] owner-root)
  rtp/PRuntimeCells
  (allocate-runtime-cell! [this value options] (allocate-cell! this value options))
  (runtime-cell-present? [this id] (cell-present? this id))
  (runtime-cell-value [this id] (read-cell-value this id))
  (runtime-cell-meta [this id] (read-cell-meta this id))
  (runtime-cell-watches [this id] (read-cell-watches this id))
  (swap-runtime-cell! [this ref id f args] (swap-cell! this ref id f args))
  (cas-runtime-cell! [this ref id old-value new-value] (cas-cell! this ref id old-value new-value))
  (add-runtime-cell-watch! [this id key f] (add-cell-watch! this id key f))
  (remove-runtime-cell-watch! [this id key] (remove-cell-watch! this id key))
  rtp/PState
  (get-state [this path] (read-application-state this path))
  (swap-state! [this path f] (swap-application-state! this path f nil))
  (swap-state-args! [this path f args] (swap-application-state! this path f args))
  (cas-state! [this path old-value new-value] (cas-application-state! this path old-value new-value)))
(def w [:w 0])
(def root [:root w])
(def cancelled ::cancelled)

#?(:clj
   (defmacro runtime-field [rt field]
     ;; Stable facade fields are direct. Everything retaining engine objects is
     ;; behind the same cell for canonical and assoc-decorated runtime views.
     (let [owned-tag (if (:ns &env) 'org.replikativ.spindel.engine.impl.owned/OwnedRuntime
                         'org.replikativ.spindel.engine.impl.owned.OwnedRuntime)
           arena-tag (if (:ns &env) 'org.replikativ.spindel.engine.impl.owned/ArenaState
                         'org.replikativ.spindel.engine.impl.owned.ArenaState)
           owned (with-meta rt (assoc (meta rt) :tag owned-tag))
           target (if (#{:gate :world :root :family-id :owner-root :arena-cell} field)
                    owned
                    (let [cell (list '.-arena-cell owned)
                          state (if (:ns &env)
                                  (list 'cljs.core/deref cell)
                                  (list '.deref (with-meta cell {:tag 'clojure.lang.Volatile})))]
                      (with-meta state {:tag arena-tag})))]
       (with-meta (list (symbol (str ".-" (name field))) target) (meta &form)))))

#?(:clj
   (defmacro locked [rt & body]
     (if (:ns &env) `(do ~@body) `(locking (runtime-field ~rt :gate) ~@body))))

(defn runtime
  ([] (runtime {}))
  ([{:keys [audit? record-audit? world-id cps-exit? on-finalization-result bindings metadata timer-transport] :or {record-audit? true world-id w}}]
   (let [family (id-dict) gate #?(:clj (Object.) :cljs nil)
         arena (->ArenaState
                (id-dict) (dict) (queue) (queue) (queue)
                #?(:clj (java.util.PriorityQueue.
                         11 (reify java.util.Comparator
                              (compare [_ x y]
                                (compare (long (a x n-rank)) (long (a y n-rank))))))
                   :cljs (array))
                (atom false)
                (doto (slots 12)
                  (put 9 (when audit? (queue))) (put 8 (members)) (put 0 (queue))
                  (put 4 (slots 32)) (put 5 (slots 14)) (put 1 0) (put 2 0)
                  (put 3 (when audit? (id-dict))) (put 6 (members)) (put 7 (id-dict)))
                (when audit? (atom (when record-audit? []))) (when audit? (members))
                (doto (slots 2) (put 0 0) (put 1 0)) (doto (slots 5) (put 3 world-id))
                family nil (id-dict)
                {:parent nil :root world-id :mode :root :cut nil :basis nil} (queue)
                (dict) (queue)
                (->RuntimeFamily gate family #?(:clj (java.util.WeakHashMap.) :cljs (js/WeakMap.))
                                 ;; Shared dirty-ID queue, value-keyed dedup,
                                 ;; sweeping flag, publication pause depth, receipt count.
                                 (doto (slots 5) (put 0 (queue)) (put 1 (id-dict))
                                       (put 2 false) (put 3 0) (put 4 0)))
                (doto (slots 6) (put 0 (queue)) (put 1 (members)) (put 2 (members))
                      (put 3 (members)) (put 4 (queue)) (put 5 (dict)))
                (atom {:values {} :shadowed #{} :map-groups #{}})
                (when cps-exit?
                  (doto (slots 5) (put 0 (id-dict)) (put 1 (id-dict)) (put 2 (queue))
                        (put 3 (id-dict)) (put 4 on-finalization-result)))
                (doto (slots 3) (put 0 (id-dict)) (put 1 (id-dict)) (put 2 false)) (slots 1)
                (doto (slots 3) (put 0 (id-dict))
                      (put 1 (or timer-transport timer-transport/default-transport)) (put 2 (queue)))
                (doto (slots 7) (put 0 :live) (put 4 0) (put 5 (id-dict))) (volatile! nil))
         rt (->OwnedRuntime gate world-id [:root world-id]
                            #?(:clj (Object.) :cljs (js-obj)) (->RootOwner [:root world-id])
                            (volatile! arena))
         rt (cond-> rt bindings (assoc :bindings bindings) metadata (assoc :metadata metadata))]
     (assoc! family world-id rt)
     rt)))

(defn- world-open! [rt]
  (when-not (and (= :live (a (runtime-field rt :lifecycle) 0))
                 (not (custody-world-phase rt)))
    (throw (ex-info "Execution world is released" {:error :world-released}))))

(defn release-context-backend [rt]
  (->OwnedRuntime (runtime-field rt :gate) (runtime-field rt :world) (runtime-field rt :root)
                  (runtime-field rt :family-id) (runtime-field rt :owner-root) (runtime-field rt :arena-cell)))

(defn pending-release-count [] (count @pending-releases))

(defn auditing? [rt]
  (boolean (runtime-field rt :audit)))

(defn audit-trace [rt]
  (when-let [audit (runtime-field rt :audit)] @audit))

(defn- enqueue-cell-gc! [rt id]
  (let [gc (:cell-gc (runtime-field rt :home))]
    (when-not (find! (a gc 1) id)
      ;; IDs are values on CLJS too: distinct keyword objects can identify the
      ;; same allocation, so the queue must not use an identity-members set.
      (assoc! (a gc 1) id true)
      (push! (a gc 0) id))))

(defn- note-cell-gc-blocker-change! [rt id]
  ;; Future world-release or lineage-visibility transitions must enqueue their
  ;; affected pending IDs here; ordinary boundaries never rediscover them by scan.
  (when (pos? (long (a (:cell-gc (runtime-field rt :home)) 4)))
    (enqueue-cell-gc! rt id)))

(defn- put-cell-gc-receipt! [rt id allocation]
  (let [state (runtime-field rt :managed-cells)
        gc (:cell-gc (runtime-field rt :home))]
    (when-not (find! (a state 1) id)
      (put gc 4 (inc (long (a gc 4)))))
    (assoc! (a state 1) id allocation)
    (put state 2 true)
    (enqueue-cell-gc! rt id)))

(defn- clear-cell-gc-receipt! [rt id]
  (let [state (runtime-field rt :managed-cells)
        gc (:cell-gc (runtime-field rt :home))]
    (when (find! (a state 1) id)
      (dissoc! (a state 1) id)
      (put gc 4 (dec (long (a gc 4))))
      ;; Clearing even a stale ancestor receipt can unblock a descendant.
      (enqueue-cell-gc! rt id))))

(defn- multiple-cell-worlds? [rt]
  (let [worlds (runtime-field rt :family)]
    #?(:clj (> (.size ^java.util.Map worlds) 1)
       :cljs (let [buckets (.-buckets worlds)]
               (or (> (.-size buckets) 1)
                   ;; If all world IDs hash alike, the sole bucket still
                   ;; records its entries as alternating ID/value pairs.
                   (> (.-length (.get buckets (hash (runtime-field rt :world)))) 2))))))

(defn- note-cell-removal! [rt id]
  (when (or (pos? (long (a (:cell-gc (runtime-field rt :home)) 4)))
            (multiple-cell-worlds? rt))
    (enqueue-cell-gc! rt id)))

(defn- next-number! [rt i]
  (if (zero? i)
    (put (runtime-field rt :serial) 0 (inc (long (a (runtime-field rt :serial) 0))))
    (put (runtime-field rt :counters) i (inc (long (a (runtime-field rt :counters) i))))))
(defn- root-owner? [owner] (instance? RootOwner owner))
(defn- scope-owner? [owner] (instance? ScopeOwner owner))
(defn- owner-storage [owner] (if (scope-owner? owner) (.-data ^ScopeOwner owner) owner))
(defn- owner-parent [owner]
  (when (and owner (not (root-owner? owner))) (a (owner-storage owner) r-owner)))
(defn- scope-state [rt] @(runtime-field rt :execution-scopes))
(defn- scope-children [rt owner]
  (when-let [state (scope-state rt)] (find! (a state 1) owner)))
(defn- scope-parent! [rt scope parent]
  (let [state (scope-state rt) data (owner-storage scope) previous (a data s-parent)]
    (when previous
      (when-let [children (scope-children rt previous)]
        (remove! children scope)
        (when (zero? (count! children)) (dissoc! (a state 1) previous))))
    (put data s-parent parent)
    (when parent
      (let [children (or (scope-children rt parent) (assoc! (a state 1) parent (members)))]
        (add! children scope)))))
(defn- execution-runtime [rt] (if (current-activation) (a (current-activation) 0) rt))
(defn- parent-node [rt id]
  (loop [parent (runtime-field rt :parent)]
    (when parent (or (find! (runtime-field parent :nodes) id) (recur (runtime-field parent :parent))))))

(defn- work-status? [status] (case status (:running :parked) true false))
(defn- active-status? [status] (case status (:running :parked :inherited :stale) true false))
(defn- resumable-status? [status] (case status (:parked :inherited) true false))
(defn- basis-status? [status] (case status (:completed :stale) true false))
(defn- fork-busy-status? [status] (case status (:running :unwinding :inherited) true false))

(defn- current [node] (a node n-current))
(defn- open-owner? [owner]
  (or (root-owner? owner)
      (and owner (if (scope-owner? owner) (a (owner-storage owner) s-open)
                     (not= :unwinding (a owner r-status))))))
(defn- mark-graph! [rt node]
  (when (and node (not (a node n-graph-dirty)))
    (put node n-graph-dirty true) (push! (a (runtime-field rt :liveness) 0) node)))

(defn- mark! [rt node]
  (when (and node (not (a node n-work)))
    (put node n-work true) (push! (runtime-field rt :work) node)))

(defn- owner-node [owner]
  (loop [owner owner]
    (cond (or (nil? owner) (root-owner? owner)) nil
          (scope-owner? owner) (recur (owner-parent owner))
          :else (a owner r-node))))
(defn- root-connected-owner? [owner]
  (loop [owner owner]
    (cond (root-owner? owner) true
          (scope-owner? owner) (and (open-owner? owner) (recur (owner-parent owner)))
          :else false)))
(defn- scope-owned-nodes [rt owner]
  (mapcat (fn visit [scope]
            (concat (items (a (owner-storage scope) s-owned))
                    (mapcat visit (when-let [children (scope-children rt scope)] (items children)))))
          (when-let [children (scope-children rt owner)] (items children))))

(defn- reactive-kind? [kind] (or (= :track kind) (= :await-reactive kind)))
(defn- reactive? [run] (boolean (and run (pos? (long (or (a run r-reactives) 0))))))
(defn- reactive-delta! [run delta]
  (put run r-reactives (+ (long (or (a run r-reactives) 0)) (long delta))))
(declare drain! wanted? retire! cancel! reclaim! snapshot snapshot-family schedule! adopt! collect-token! collect-home-token! map-value run-id owner-id
         retain-cleanup! queue-cleanup! cleanup-adopt! cleanup-return!
         invoke-cleanup! finish-cleanup-slice! cleanup-cell! profile-view boundary! deliver-value! complete! finish-slice! release-cleanup!)

(defn- clear-live-set! [live slot]
  (let [before (a live slot)]
    (if (> (count! before) 64) (put live slot (members)) (clear-members! before))))

(defn- invalidate-liveness! [rt]
  (let [live (runtime-field rt :liveness)]
    (clear-live-set! live 1) (clear-live-set! live 2) (clear-live-set! live 3)))

(defn- owns-live-kind? [node]
  (or (not= :spin (a node n-kind)) (not (a node n-complete)) (a node n-kept)))

(defn- retain-link! [rt links target]
  (when (and target (identical? target (find! (runtime-field rt :nodes) (a target n-id))))
    (add! links target)))

(defn- retain-scope-links! [rt links scopes]
  (each! [scope scopes]
         (each! [child (a (owner-storage scope) s-owned)]
                (when (and (open-owner? (a child n-owner)) (owns-live-kind? child))
                  (retain-link! rt links child)))
         (when-let [children (scope-children rt scope)]
           (when-not (empty-native? children) (retain-scope-links! rt links children)))))

(defn- reconcile-retention! [rt]
  (let [pending (a (runtime-field rt :liveness) 0)]
    (loop []
      (when-let [node (pop! pending)]
        (put node n-graph-dirty false)
        (let [before (a node n-links) next (a node n-link-buffer)
              present? (identical? node (find! (runtime-field rt :nodes) (a node n-id)))
              owner (a node n-owner)
              external? (boolean
                         (and present?
                              (or (and (root-connected-owner? owner) (owns-live-kind? node))
                                  (any! (a node n-dependents) #(and (a % o-live) (nil? (a % o-run)))))))]
          (clear-members! next)
          (when present?
            (when (and owner (not (root-owner? owner)))
              (retain-link! rt next (owner-node owner)))
            (each! [run (values (a node n-runs))]
                   (when-not (= :unwinding (a run r-status))
                     (let [owner (a run r-owner)]
                       (when (and owner (not (root-owner? owner)))
                         (retain-link! rt next (owner-node owner))))
                     (each! [ob (a run r-obs)]
                            (when (a ob o-live) (retain-link! rt next (a ob o-debtor))))
                     (each! [child (a run r-owned)]
                            (when (and (open-owner? (a child n-owner)) (owns-live-kind? child))
                              (retain-link! rt next child)))
                     (when-let [scopes (scope-children rt run)]
                       (when-not (empty-native? scopes) (retain-scope-links! rt next scopes))))))
          (when-not (= external? (boolean (a node n-external-root)))
            (put node n-external-root external?) (invalidate-liveness! rt))
          (if (and (= (count! before) (count! next))
                   (not (any! before #(not (has? next %)))))
            (clear-members! next)
            (do
              (invalidate-liveness! rt)
              (each! [target before]
                     (when-not (has? next target)
                       (let [supporters (a target n-supporters)]
                         (remove! supporters node)
                         ;; Drop backing storage after wide fan-out contracts.
                         (when (or (zero? (count! supporters)) (= 64 (count! supporters)))
                           (let [small (members)]
                             (each! [entry supporters] (add! small entry))
                             (put target n-supporters small))))))
              (each! [target next]
                     (when-not (has? before target) (add! (a target n-supporters) node)))
              (if (and (> (count! before) 64) (<= (count! next) 64))
                (let [small (members)]
                  (each! [target next] (add! small target))
                  (put node n-links small) (put node n-link-buffer (members)))
                (do (put node n-links next) (put node n-link-buffer before)
                    (clear-members! before)))))
          (when-not present? (put node n-supporters (members))))
        (recur)))))

(defn- dict-has? [m key]
  #?(:clj (.containsKey ^java.util.Map m key) :cljs (.has m key)))

(defn- remember-live-path! [cache parents node]
  (loop [node node]
    (when node (add! cache node) (recur (find! parents node)))))

(defn- find-live-root! [rt node]
  (let [live (runtime-field rt :liveness) external (a live 1) work (a live 2) absent (a live 3)
        pending (a live 4) parents (a live 5)]
    (push! pending node) (assoc! parents node nil)
    (try
      (loop []
        (if-let [candidate (pop! pending)]
          (cond
            (or (a candidate n-external-root) (has? external candidate))
            (do (remember-live-path! external parents candidate) true)
            (or (active-status? (some-> (current candidate) (a r-status))) (has? work candidate))
            (do (remember-live-path! work parents candidate) true)
            (has? absent candidate) (recur)
            :else
            (do (each! [supporter (a candidate n-supporters)]
                       (when-not (dict-has? parents supporter)
                         (assoc! parents supporter candidate) (push! pending supporter)))
                (recur)))
          (do
            (doseq [candidate #?(:clj (.keySet ^java.util.Map parents)
                                 :cljs (array-seq (js/Array.from (.keys parents))))]
              (add! absent candidate))
            false)))
      (finally
        #?(:clj (.clear ^java.util.ArrayDeque pending) :cljs (.clear pending))
        (if (> #?(:clj (.size ^java.util.Map parents) :cljs (.-size parents)) 64)
          (put live 5 (dict))
          #?(:clj (.clear ^java.util.Map parents) :cljs (.clear parents)))))))

(defn- wanted? [node]
  (let [rt (a node n-runtime) live (runtime-field rt :liveness)]
    (reconcile-retention! rt)
    (or (a node n-external-root)
        (active-status? (some-> (current node) (a r-status)))
        (has? (a live 1) node) (has? (a live 2) node)
        (and (not (has? (a live 3) node)) (find-live-root! rt node)))))

(defn- add-run! [run field member]
  (let [before (a run field)
        set (if (identical? before empty-members) (put run field (members)) before)]
    (add! set member)
    (when (> (count! set) 64) (put run r-wide true))))

(defn- owner! [rt node owner]
  (let [old (a node n-owner)]
    (when-not (identical? old owner)
      (when (or (not= (root-connected-owner? old) (root-connected-owner? owner))
                (not (identical? (owner-node old) (owner-node owner)))
                (not= (boolean (open-owner? old)) (boolean (open-owner? owner))))
        (mark-graph! rt node) (mark-graph! rt (owner-node old)) (mark-graph! rt (owner-node owner)))
      (when (and old (not (root-owner? old)))
        (remove! (a (owner-storage old) r-owned) node)
        (when-let [parent (owner-node old)] (mark! rt parent)))
      (put node n-owner owner)
      (when (and owner (not (root-owner? owner)))
        (if (scope-owner? owner) (add! (a (owner-storage owner) s-owned) node)
            (add-run! owner r-owned node))
        (when-let [parent (owner-node owner)] (mark! rt parent)))
      (mark! rt node))))

(defn- kept! [rt node value]
  (when-not (= (boolean value) (boolean (a node n-kept)))
    (mark-graph! rt node) (mark-graph! rt (owner-node (a node n-owner))))
  (put node n-kept value))

(defn- node! [rt id kind owner]
  (world-open! rt)
  (let [node (slots 37)]
    (put node n-id id) (put node n-runtime rt) (put node n-kind kind) (put node n-complete false)
    (put node n-kept false) (put node n-tokens (members)) (put node n-order 0)
    (put node n-created-by (members)) (put node n-creator-refs (dict))
    (put node n-runs (dict)) (put node n-dependents (members))
    (put node n-links (members)) (put node n-link-buffer (members)) (put node n-supporters (members))
    (put node n-generation 0) (put node n-rank 0)
    (assoc! (runtime-field rt :nodes) id node) (mark-graph! rt node) (owner! rt node owner) node))

(defn- creator! [rt node creator]
  (let [old (a node n-creator)
        source (when creator (if (vector? creator) (find! (runtime-field rt :nodes) (nth creator 0)) (a creator r-node)))]
    (when-not (identical? old creator)
      (doseq [[value source delta] [[old (a node n-creator-source) -1] [creator source 1]]
              :when (and value source)]
        (let [gen (if (vector? value) (nth value 1) (a value r-gen))
              refs (a source n-creator-refs) n (+ delta (long (or (find! refs gen) 0)))]
          (if (zero? n) (dissoc! refs gen) (assoc! refs gen n))
          (add! (a (runtime-field rt :counters) 8) source)))
      (put node n-creator creator)
      (put node n-creator-source source))))

(defn- prune-ancestry! [rt]
  (each! [node (a (runtime-field rt :counters) 8)]
         (each! [run (values (a node n-runs))]
                (each-copy! [gen (a run r-ancestors)]
                            (when-not (or (when-let [live (find! (a node n-runs) gen)] (not= :unwinding (a live r-status)))
                                          (find! (a node n-creator-refs) gen))
                              (remove! (a run r-ancestors) gen)))))
  (clear-members! (a (runtime-field rt :counters) 8)))

(defn- creation! [run node]
  (add-run! run r-created node) (add! (a node n-created-by) run))
(defn- uncreate! [run node]
  (remove! (a run r-created) node) (remove! (a node n-created-by) run))

(defn- exit-id [rt run] [:cps-exit (runtime-field rt :world) (run-id run)])
;; Run arrays and ScopeOwner values have identity equality. These lexical
;; frames freeze ancestry evidence during a cascade, never admission authority.
(def ^:private ^:dynamic *retiring-owners* {})

(defn- run-anchor [rt run]
  (loop [owner run chain []]
    (cond (nil? owner) (conj chain (runtime-field rt :world))
          (get *retiring-owners* owner) (into chain (get *retiring-owners* owner))
          (root-owner? owner) (conj chain (:id owner) (runtime-field rt :world))
          (scope-owner? owner) (recur (owner-parent owner) (conj chain (a (owner-storage owner) s-id)))
          (= :unwinding (a owner r-status)) (into chain (a owner r-anchor))
          :else (recur (a owner r-owner) (conj chain (run-id owner))))))

(defn- empty-dict? [m]
  #?(:clj (.isEmpty ^java.util.Map m)
     :cljs (zero? (.-size (if (instance? IDMap m) (.-buckets m) m)))))

(defn- queue-cleanup! [rt ticket]
  (when (and (= :ready (a ticket x-phase)) (not (a ticket x-physical))
             (or (nil? (a ticket x-operation)) (zero? (long (a (a ticket x-operation) p-physical))))
             (not (a ticket x-queued)))
    (put ticket x-queued true)
    (push! (a (runtime-field rt :finalization) 2) ticket)))

(defn- install-cancel-reason! [ticket cancellation]
  (when (and cancellation (nil? (a ticket x-cancel-value)))
    (put ticket x-cancel-value [(:reason cancellation)])
    (put ticket 14 (:reason cancellation))))

(defn- reserve-exit!
  ([rt run] (reserve-exit! rt run nil))
  ([rt run cancellation]
   (when (and (a run r-entered) (#{:running :parked :stale} (a run r-status)))
     (let [ticket (or (a run r-exit)
                      (doto (slots 18)
                        (put x-id (exit-id rt run)) (put x-anchor (run-anchor rt run))
                        (put x-phase :ready) (put x-seq (or (a run r-finalization-seq) 0))
                        (put x-reject (a run r-cancel-cont)) (put x-run run)
                        (put x-address (a run r-address))
                        (put x-cells (id-dict))
                        (put 14 (if cancellation (:reason cancellation)
                                    (ex-info "Cancelled" {:error :cancelled})))))]
       (put run r-exit ticket)
       (install-cancel-reason! ticket cancellation)
       (when (and (nil? (a ticket x-cancel-value)) (not (a ticket 14)))
         (put ticket 14 (if cancellation (:reason cancellation)
                            (ex-info "Cancelled" {:error :cancelled}))))
       (put ticket x-kind :cps-exit) (put ticket x-run nil) (put ticket x-physical (boolean (a run r-physical)))
       (assoc! (a (runtime-field rt :finalization) 0) (a ticket x-id) ticket)
       (queue-cleanup! rt ticket)
       ticket))))

(defn- owner-child-runs [owner]
  (if (root-owner? owner) empty-members (a (owner-storage owner) r-childruns)))
(defn- unfinished-cps-subtree? [rt owner]
  (or (and (not (root-owner? owner)) (not (scope-owner? owner))
           (a owner r-entered) (#{:running :parked :stale} (a owner r-status)))
      (any! (owner-child-runs owner) #(unfinished-cps-subtree? rt %))
      (when-let [children (scope-children rt owner)]
        (any! children #(unfinished-cps-subtree? rt %)))))

(defn- source-allocation [rt id]
  (if-let [aux (find! (a (runtime-field rt :managed-cells) 0) id)]
    (a aux 0)
    (when-let [profile (runtime-field rt :finalization)] (find! (a profile 3) id))))

(defn- retain-cleanup!
  ([rt root-run] (retain-cleanup! rt root-run nil))
  ([rt root-run cancellation]
   (when-let [profile (runtime-field rt :finalization)]
     (when (or (not (empty-dict? (a profile 0))) (unfinished-cps-subtree? rt root-run))
    ;; Capture the whole subtree before recursive retirement mutates ownership.
       (let [owners (members) identities (id-dict)]
         (letfn [(visit [run]
                   (when-not (has? owners run)
                     (add! owners run) (assoc! identities (owner-id run) true)
                     (each! [child (owner-child-runs run)] (visit child))
                     (each! [child (or (scope-children rt run) empty-members)] (visit child))))]
           (visit root-run))
         (each! [run owners]
                (when-not (or (root-owner? run) (scope-owner? run))
                  (reserve-exit! rt run (when (and cancellation
                                                   (identical? (:node cancellation) (a run r-node)))
                                          cancellation))))
         (let [participants (filter #(and (= :cps-exit (a % x-kind))
                                          (some (fn [id] (find! identities id)) (a % x-anchor)))
                                    (values (a profile 0)))
               cells (id-dict)]
           (each! [run owners]
                  (each! [node (if (root-owner? run) empty-members (a (owner-storage run) r-owned))]
                         (when (#{:signal :atom :deferred :mailbox} (a node n-kind))
                           (let [key [(runtime-field rt :world) (owner-id run) (a node n-id)]
                                 cell (or (find! (a profile 1) key)
                                          (let [cell (doto (slots (if (#{:deferred :mailbox} (a node n-kind)) 5 4))
                                                       (put 0 (a node n-kind)) (put 1 (a node n-value))
                                                       (put 2 (members)) (put 3 (source-allocation rt (a node n-id))))]
                                            (when (#{:deferred :mailbox} (a node n-kind))
                                              (put cell 4 (a node (if (= :mailbox (a node n-kind)) n-mailbox n-deferred))))
                                            cell))]
                             (assoc! cells key cell)))))
           (doseq [receipt (values (a profile 0))
                   :when (and (= :mailbox-callback (a receipt x-kind))
                              (some (fn [id] (find! identities id)) (a receipt x-anchor)))]
             ;; A raw consumer retains its named Mailbox, not its owner's
             ;; neighboring application payloads or ownership graph.
             (put receipt 20 true))
           (doseq [ticket participants]
             (doseq [[key cell] (map-value (a ticket x-cells))] (assoc! cells key cell)))
           (doseq [[key cell] (map-value cells) :when (seq participants)]
             (assoc! (a profile 1) key cell)
             (doseq [ticket participants]
               (add! (a cell 2) ticket) (assoc! (a ticket x-cells) key cell)))))))))

(defn- cleanup-adopt! [rt run]
  (when-let [ticket (a run r-exit)]
    (when (and (= :cps-exit (a ticket x-kind)) (= :ready (a ticket x-phase)))
      (let [frame (current-activation)]
        (when-not (and frame (identical? rt (a frame 0)) (identical? run (a frame 1))
                       (a run r-physical) (nil? (a frame 8)))
          (throw (ex-info "Cleanup adoption requires the exact physical slice" {})))
        (end-deferred-protection! rt ticket)
        (put ticket x-phase :claimed) (put frame 8 ticket) (put (runtime-field rt :thread) 4 ticket)
        (boundary! rt (when (runtime-field rt :audit) {:t :cleanup-adopt :n (a ticket x-id) :th :engine}))))
    ticket))

(defn- cleanup-return! [rt ticket value failed?]
  (when-not (= :claimed (a ticket x-phase))
    (throw (ex-info "Cleanup completion requires a claimed ticket" {})))
  ;; This reports the terminal CPS outcome, which may be the body's original
  ;; rejection. Attributing a new finalizer failure requires compiler ownership
  ;; metadata and remains a public-adapter gate. Never guess from user payloads.
  (when-let [observer (a (runtime-field rt :finalization) 4)]
    (push! (runtime-field rt :hosts)
           (doto (slots 2) (put 0 observer)
                 (put 1 {:owner [(runtime-field rt :world) (nth (a ticket x-id) 2)]
                         :failed? failed? :value value}))))
  (put ticket x-phase :returning) (put ticket x-delivered false) (put ticket x-value nil)
  (put ticket x-resolve nil) (put ticket x-reject nil)
  (boundary! rt (when (runtime-field rt :audit) {:t :cleanup-return :th :engine})))

(defn- release-ticket-cells! [rt ticket]
  (end-deferred-protection! rt ticket)
  (let [profile (runtime-field rt :finalization)]
    (doseq [[key cell] (map-value (a ticket x-cells))]
      (remove! (a cell 2) ticket)
      (when (zero? (count! (a cell 2))) (dissoc! (a profile 1) key)))
    (doseq [key (keys (map-value (a ticket x-cells)))] (dissoc! (a ticket x-cells) key))))

(defn- release-cleanup! [rt ticket]
  (release-ticket-cells! rt ticket)
  (dissoc! (a (runtime-field rt :finalization) 0) (a ticket x-id))
  (put ticket x-run nil) (put ticket 14 nil) (put ticket x-address nil) (put ticket x-cancel-value nil))

(defn- cleanup-cell! [rt source]
  (let [frame (current-activation)
        ticket (when (and frame (not (active-operation)) (identical? rt (a frame 0)))
                 (or (a frame 8) (when-let [run (a frame 1)]
                                   (when (= :unwinding (a run r-status)) (cleanup-adopt! rt run)))))]
    (when-let [ticket (or (when-let [receipt (active-mailbox-callback)]
                            (mailbox-callback-check! rt receipt) receipt)
                          (when-let [operation (active-operation)]
                            (when (operation-retired? operation)
                              (operation-check! rt operation) (a operation p-ticket)))
                          ticket)]
      (when-not (or (active-operation) (active-mailbox-callback) (= :claimed (a ticket x-phase)))
        (throw (ex-info "Cleanup is not executing" {})))
      (or (first (for [[key cell] (map-value (a ticket x-cells))
                       :when (and (= (:id source) (nth key 2))
                                  (if (#{:atom :deferred :mailbox} (a cell 0))
                                    (= (:allocation source) (a cell 3))
                                    (identical? (:allocation source) (a cell 3))))] [key cell]))
          (throw (ex-info "Source is outside the retained cleanup view" {:error :missing-cleanup-cell :id (:id source)}))))))

(defn- profile-view [rt]
  (when-let [profile (runtime-field rt :finalization)]
    {:native (into {} (for [ticket (values (a profile 0))]
                        [(a ticket x-id)
                         (if (= :mailbox-callback (a ticket x-kind))
                           (let [consumer (a ticket 18)]
                             (cond-> {:kind :mailbox-callback :owner [(runtime-field rt :world) (a ticket 19)]
                                      :state :running :anchor (a ticket x-anchor) :cells (set (keys (map-value (a ticket x-cells))))
                                      :consumer (a consumer b-id) :allocation (a consumer b-allocation)
                                      :frame (a consumer b-frame) :consumer-kind (a consumer b-kind) :retired? (boolean (a ticket 20))
                                      :phase (a ticket x-phase) :physical? (boolean (a ticket x-physical))
                                      :variant (if (#{:rejection-queued :rejection-entered} (a consumer b-state)) :error :ok)}
                               (#{:rejection-queued :rejection-entered} (a consumer b-state))
                               (assoc :delivery (a consumer b-error-receipt))))
                           (cond-> {:kind (a ticket x-kind) :owner [(runtime-field rt :world) (nth (a ticket x-id) 2)]
                                    :state :running :phase (a ticket x-phase) :sequence (a ticket x-seq)
                                    :retired? (= :cps-exit (a ticket x-kind)) :anchor (a ticket x-anchor)}
                             (seq (map-value (a ticket x-cells))) (assoc :cells (set (keys (map-value (a ticket x-cells)))))
                             (a ticket x-cancel-value) (assoc :cancel-value (diagnostic-value (first (a ticket x-cancel-value)) true))
                             (a ticket x-operation)
                             (assoc :operation
                                    (let [operation (a ticket x-operation)]
                                      (cond-> {:id (a operation p-id) :state (a operation p-state)
                                               :parent (a operation p-parent) :physical (a operation p-physical)
                                               :frames (a operation p-frames)
                                               :next-registration (a operation p-next) :next-frame (a operation p-frame-next)
                                               :registrations (into {} (for [registration (values (a operation p-registrations))]
                                                                         [(a registration g-id)
                                                                          (cond-> {:w (runtime-field rt :world)
                                                                                   :e (a registration g-allocation)
                                                                                   :allocation (a registration g-allocation)
                                                                                   :cell (a registration g-key)
                                                                                   :state (a registration g-state) :entered? (boolean (a registration g-entered))
                                                                                   :continuation (a registration g-id)}
                                                                            (and (a registration g-mailbox) (a (a registration g-mailbox) b-message))
                                                                            (assoc :message-id (first (a (a registration g-mailbox) b-message)))
                                                                            (#{:ready :claimed} (a registration g-state))
                                                                            (assoc :delivery (diagnostic-value (a registration g-value) false)))]))}
                                        (= :terminal (a operation p-state)) (assoc :variant (a operation p-terminal)))))
                             (a ticket x-delivered) (assoc :delivery (diagnostic-value (a ticket x-value) (a ticket x-failed)))))]))
     :cleanup-cells (into {} (for [[key cell] (map-value (a profile 1))]
                               [key (cond-> {:kind (a cell 0) :result (if (= :deferred (a cell 0)) (a (a cell 4) 2) (a cell 1))
                                             :holders (set (map #(a % x-id) (items (a cell 2))))}
                                      (= :deferred (a cell 0))
                                      (assoc :allocation (a cell 3) :deferred (assoc (deferred-metadata (a cell 4))
                                                                                     :assigned? (boolean (a (a cell 4) 1))))
                                      (= :mailbox (a cell 0)) (assoc :allocation (a cell 3) :mailbox (mailbox-metadata (a cell 4))))]))}))

(defn- end-ob! [rt ob]
  (when (a ob o-live)
    (when-let [timer (a ob o-timer)] (timer-revoke! rt timer))
    (when-let [consumer (a ob o-mailbox)]
      (when-not (#{:claimed :entered} (a consumer b-state)) (mailbox-detach! rt consumer)))
    (put ob o-live false)
    (when (= :await-once (a ob o-kind))
      (dissoc! (runtime-field rt :deliveries) (a ob o-id))
      (when-let [operation (find! (runtime-field rt :operations) (a ob o-id))]
        (dissoc! (runtime-field rt :operations) (a ob o-id))
        (if (= :consumed (a ob o-slot))
          (put operation 0 :settled)
          (do (put operation 0 :cancelled)
              (when-let [cancel (a operation 1)] (push! (runtime-field rt :posts) (doto (slots 1) (put 0 cancel))))))
        (put operation 1 nil)))
    (when-let [run (a ob o-run)]
      (remove! (a run r-obs) ob)
      (when (reactive-kind? (a ob o-kind)) (reactive-delta! run -1))
      (mark! rt (a run r-node)))
    (when (= :await-once (a ob o-kind))
      (let [host (a ob o-host)]
        (when-let [waiters (find! (runtime-field rt :tickets) host)]
          (remove! waiters ob)
          (when (zero? (count! waiters)) (dissoc! (runtime-field rt :tickets) host)))))
    (when-let [node (a ob o-debtor)]
      (remove! (a node n-dependents) ob) (mark! rt node)
      (when (#{:atom :deferred :mailbox} (a node n-kind))
        (note-cell-gc-blocker-change! rt (a node n-id)))
      (if-let [creditor (a ob o-creditor-node)]
        (when-not
         ;; Search the smaller adjacency. A shared source can have thousands
         ;; of dependents while each creditor has only one outgoing edge.
         (if (and (current creditor)
                  (< (count! (a (current creditor) r-obs)) (count! (a node n-dependents))))
           (any! (values (a creditor n-runs))
                 (fn [run]
                   (any! (a run r-obs) #(and (a % o-live) (identical? node (a % o-debtor))))))
           (any! (a node n-dependents)
                 #(and (a % o-live) (identical? creditor (a % o-creditor-node)))))
          (mark-graph! rt creditor))
        (when-not (any! (a node n-dependents) #(and (a % o-live) (nil? (a % o-run))))
          (mark-graph! rt node))))))

(defn- reject-dependent!
  ([rt ob] (reject-dependent! rt ob *world-release-cancellation*))
  ([rt ob cancellation]
   (if-let [run (a ob o-run)]
     (do
       (when (and (= :consumed (a ob o-slot)) (= :await-reactive (a ob o-kind))
                  (#{:running :parked :inherited :completed} (a run r-status)) (identical? run (current (a run r-node))))
         (put run r-validation-lost true)
         (when (a (a run r-node) n-complete) (put (a run r-node) n-dirty true)))
       (when (and (= :armed (a ob o-slot))
                  (or (= :parked (a run r-status))
                      (and (= :running (a run r-status)) (a ob o-mailbox)
                           (= :reserved (a (a ob o-mailbox) b-state)))))
         (put run r-status :running)
         (put ob o-value (if cancellation (:reason cancellation)
                             (ex-info "Cancelled" {:error :cancelled})))
         (put ob o-delivery-error true) (put ob o-slot :consumed)
         (when (= :await-reactive (a ob o-kind))
           (put run r-validation-lost true)
           (when (a (a run r-node) n-complete) (put (a run r-node) n-dirty true)))
         (schedule! rt (a run r-node) ob)))
     (if-let [consumer (a ob o-mailbox)]
       (when (#{:pending :reserved} (a consumer b-state))
         (queue-mailbox-rejection! rt consumer
                                   (if cancellation (:reason cancellation) (ex-info "Cancelled" {}))
                                   (if cancellation :explicit :cancelled)))
       (push! (runtime-field rt :hosts)
              (doto (slots 2) (put 0 (a ob o-failure))
                    (put 1 (if cancellation (:reason cancellation) (ex-info "Cancelled" {})))))))
   (end-ob! rt ob)))

(defn- release-owned! [rt run]
  (each-copy! [node (if (custody-state rt)
                      (custody-order (a (owner-storage run) r-owned) #(a % n-id))
                      (a (owner-storage run) r-owned))]
              (when-let [control (a node n-mailbox)]
                (doseq [consumer (vec (concat (values (a control m-pending)) (values (a control m-reservations))))]
                  (refresh-mailbox-owner! rt consumer (a node n-owner))
                  ;; Queue raw rejection while the closing owner is still
                  ;; explicit. Its named holder then survives source removal;
                  ;; a returned reservation uses the original live envelope.
                  (when (and (= :host (a consumer b-kind)) (#{:pending :reserved} (a consumer b-state)))
                    (queue-mailbox-rejection! rt consumer (ex-info "Cancelled" {}) :cancelled))))
              (owner! rt node nil)
              (when-let [control (a node n-mailbox)]
                ;; Prefix adoption can move this allocation away from a raw
                ;; consumer's original join anchor. Retirement follows the
                ;; allocation as well as that immutable original anchor.
                (doseq [consumer (values (a control m-physical))]
                  (when-let [receipt (a consumer b-receipt)] (put receipt 20 true))))
              (when (= :spin (a node n-kind)) (put node n-dirty true))
              (each-copy! [child (if (custody-state rt)
                                   (custody-order (values (a node n-runs))
                                                  (fn [r] [(if (work-status? (a r r-status)) 0 1) (run-id r)]))
                                   (values (a node n-runs)))]
                          (if (work-status? (a child r-status)) (cancel! rt child) (retire! rt child)))
              (each-copy! [ob (a node n-dependents)] (reject-dependent! rt ob))))

(defn- forget-run! [rt run]
  (when-let [ticket (a run r-exit)] (put ticket x-run nil))
  (let [node (a run r-node)]
    (dissoc! (a node n-runs) (a run r-gen))
    (add! (a (runtime-field rt :counters) 8) node)
    (remove! (a (runtime-field rt :counters) 6) run)
    (when (identical? run (current node))
      (put node n-current (last (sort-by #(a % r-gen) (values (a node n-runs))))))
    (mark! rt node)
    ;; Dead obligations carry their own creditor node/generation. They never
    ;; interpret a recycled run's identity when dispatching an old trigger.
    (fields! [field [r-created r-spawned r-obs r-owned r-backlinks r-childruns r-ancestors]]
             (if (a run r-wide)
               (put run field empty-members)
               (clear-members! (a run field))))
    (put run r-wide nil)
    (fields! [field [r-node r-gen r-owner r-pred r-status r-seq r-physical r-anchor r-origin r-source-world r-reactives r-validation-lost r-entered r-finalization-seq r-exit r-cancel-cont r-address r-timers]]
             (put run field nil))
    (let [pool (a (runtime-field rt :counters) 0)]
      (when (< #?(:clj (.size ^java.util.ArrayDeque pool) :cljs (.-length pool)) 32)
        (push! pool run)))))

(defn- retire-body! [rt run cancellation chain]
  (let [cancellation (or cancellation *world-release-cancellation*)
        node (a run r-node)
        _ (when (a (runtime-field rt :counters) 11) (custody-claim-owner! rt run))
        _ (retain-cleanup! rt run cancellation)
        physical? (or (a run r-physical) (a run r-exit) (pos? (long (or (a run r-timers) 0))))
        anchor (when physical? (or chain (run-anchor rt run)))]
    (each-copy! [scope (if (custody-state rt)
                         (custody-order (or (scope-children rt run) empty-members) owner-id)
                         (or (scope-children rt run) empty-members))] (close-owner! rt scope))
    (each-copy! [ob (a run r-obs)] (end-ob! rt ob))
    (each-copy! [child (if (custody-state rt)
                         (custody-order (a run r-childruns) run-id)
                         (a run r-childruns))] (cancel! rt child))
    (release-owned! rt run)
    (each! [owner (a run r-backlinks)] (remove! (a owner r-spawned) run))
    (each! [child (a run r-spawned)] (remove! (a child r-backlinks) run))
    (each! [node (a run r-created)]
           (remove! (a node n-created-by) run)
           (when (identical? run (a node n-creator))
       ;; A surviving cache keeps the logical creator ID, not the old run's
       ;; mutable ownership graph.
             (if physical? (creator! rt node nil)
                 (put node n-creator [(a (a run r-node) n-id) (a run r-gen)]))))
    (when-let [owner (a run r-owner)]
      (when-not (root-owner? owner)
        (let [parent (owner-node owner)]
          (when (and parent (not (identical? parent (owner-node (a node n-owner))))
                     (not (any! (values (a node n-runs))
                                #(and (not (identical? run %)) (not= :unwinding (a % r-status))
                                      (identical? parent (owner-node (a % r-owner)))))))
            (mark-graph! rt node))
          (remove! (a (owner-storage owner) r-childruns) run)
          (when parent (mark! rt parent)))))
    (if physical?
      (do (put run r-status :unwinding) (put run r-owner nil) (put run r-pred nil)
          (put run r-anchor anchor)
          (add! (a (runtime-field rt :counters) 8) (a run r-node))
          (each! [successor (values (a (a run r-node) n-runs))]
                 (when (= (a run r-gen) (a successor r-pred)) (put successor r-pred nil)))
          (clear-members! (a run r-ancestors))
          (clear-members! (a run r-created))
          (clear-members! (a run r-spawned))
          (clear-members! (a run r-backlinks))
          (put run r-cancel-cont nil))
      (forget-run! rt run))
    (mark! rt (a run r-node))))

(defn- retire!
  ([rt run] (retire! rt run nil))
  ([rt run cancellation]
   ;; Test the existing frame before inspecting sets that its cascade may have
   ;; emptied. A leaf has no synchronous recursive owner-retirement edge.
   ;; Retention/registration cleanup only queue work; new synchronous teardown
   ;; or ownership paths must revisit this predicate.
   (when (and (not (contains? *retiring-owners* run))
              (has? (a (runtime-field rt :counters) 6) run) (not= :unwinding (a run r-status)))
     (let [scopes (scope-children rt run)]
       (if (and (not (custody-owner-holds? rt run))
                (zero? (count! (a run r-owned)))
                (zero? (count! (a run r-childruns)))
                (or (nil? scopes) (zero? (count! scopes))))
         (retire-body! rt run cancellation nil)
         (binding [*retiring-owners* (assoc *retiring-owners* run (run-anchor rt run))]
           (retire-body! rt run cancellation (get *retiring-owners* run))))))))

(defn- cancel! [rt run]
  (when (and (not (contains? *retiring-owners* run))
             (has? (a (runtime-field rt :counters) 6) run) (not= :unwinding (a run r-status)))
    (let [node (a run r-node) current? (identical? run (current node))
          predecessor (find! (a node n-runs) (a run r-pred))]
      (retire! rt run)
      (when current?
        (each-copy! [ob (a node n-dependents)] (reject-dependent! rt ob))
        (when (and predecessor (= :stale (a predecessor r-status))) (retire! rt predecessor)))
      (put node n-dirty true))))

(defn- drop-node-events! [rt node]
  (put node n-source-event nil)
  (when (#{:atom :deferred :mailbox} (a node n-kind))
    (note-cell-gc-blocker-change! rt (a node n-id)))
  #?(:clj (.removeIf ^java.util.Collection (runtime-field rt :events)
                     (reify java.util.function.Predicate
                       (test [_ event] (identical? node (a event 0)))))
     :cljs (.removeWhere (runtime-field rt :events) (fn [event] (identical? node (a event 0))))))

(defn- signal-dependent? [node]
  ;; Pure one-shot caches have no outgoing reactive registrations. Only idle
  ;; teardown needs this search; publication and hot reentry stay indexed.
  (when (reactive? (current node))
    (loop [todo [node] seen #{}]
      (if-let [node (peek todo)]
        (let [todo (pop todo)]
          (cond
            (contains? seen node) (recur todo seen)
            (or (#{:signal :atom :deferred :mailbox} (a node n-kind)) (a node n-dirty)) true
            :else
            (recur (into todo (for [run (values (a node n-runs))
                                    ob (items (a run r-obs))
                                    :when (and (reactive-kind? (a ob o-kind)) (a ob o-debtor))]
                                (a ob o-debtor)))
                   (conj seen node))))
        false))))

(defn- reclaim-unwanted! [rt node]
  (when (and (= :spin (a node n-kind)) (a node n-complete))
    (when (signal-dependent? node) (put node n-dirty true))
    (each-copy! [run (values (a node n-runs))] (retire! rt run))
    (owner! rt node nil)
    ;; A live descriptor supplies its body again on invocation. A value-only
    ;; cache must not keep the body's captured descriptors or resources alive.
    (put node n-body nil) (put node n-resume nil))
  (when-not (and (= :spin (a node n-kind)) (a node n-complete)
                 (pos? (count! (a node n-tokens))))
    (each-copy! [run (values (a node n-runs))] (retire! rt run))
    (each-copy! [creator (a node n-created-by)] (uncreate! creator node))
    (drop-node-events! rt node)
    (creator! rt node nil)
    (dissoc! (runtime-field rt :nodes) (a node n-id))
    (dissoc! (a (runtime-field rt :managed-cells) 0) (a node n-id))
    (when (#{:atom :deferred :mailbox} (a node n-kind))
      (note-cell-removal! rt (a node n-id)))
    (when-let [profile (runtime-field rt :finalization)] (dissoc! (a profile 3) (a node n-id)))
    (put node n-body nil) (put node n-value nil) (put node n-resume nil)
    (clear-members! (a node n-tokens))
    (mark-graph! rt node) (mark! rt node)))

(defn- reclaim! [rt]
  (let [live (runtime-field rt :liveness)]
    ;; Work roots can change at every body boundary; external proofs survive
    ;; stable logical topology even when physical run generations change.
    (clear-live-set! live 2) (clear-live-set! live 3)
    (try
      (loop []
        (when-let [node (pop! (runtime-field rt :work))]
          (put node n-work false)
          (when (and (identical? node (find! (runtime-field rt :nodes) (a node n-id))) (not (wanted? node)))
            (reclaim-unwanted! rt node))
          (recur)))
      (finally
        (reconcile-retention! rt)
        (clear-live-set! live 2) (clear-live-set! live 3)))))

(defn- audit-retention! [rt]
  (each! [node (values (runtime-field rt :nodes))]
         (let [owner (a node n-owner)
               expected (set (filter some?
                                     (concat [(owner-node owner)]
                                             (mapcat (fn [run]
                                                       (when-not (= :unwinding (a run r-status))
                                                         (concat [(owner-node (a run r-owner))]
                                                                 (for [ob (items (a run r-obs)) :when (a ob o-live)] (a ob o-debtor))
                                                                 (filter #(and (open-owner? (a % n-owner)) (owns-live-kind? %))
                                                                         (concat (items (a run r-owned)) (scope-owned-nodes rt run))))))
                                                     (values (a node n-runs))))))
               actual (set (items (a node n-links)))
               external? (boolean (or (and (root-connected-owner? owner) (owns-live-kind? node))
                                      (any! (a node n-dependents) #(and (a % o-live) (nil? (a % o-run))))))]
           (when-not (and (= expected actual) (= external? (boolean (a node n-external-root))))
             (throw (ex-info "Retention graph differs from semantic rows"
                             {:id (a node n-id) :expected (set (map #(a % n-id) expected))
                              :actual (set (map #(a % n-id) actual))
                              :root external? :actual-root (a node n-external-root)})))
           (each! [target (a node n-links)]
                  (when-not (and (identical? target (find! (runtime-field rt :nodes) (a target n-id)))
                                 (has? (a target n-supporters) node))
                    (throw (ex-info "Retention edge has no reverse index" {:id (a node n-id)}))))
           (each! [source (a node n-supporters)]
                  (when-not (and (identical? source (find! (runtime-field rt :nodes) (a source n-id)))
                                 (has? (a source n-links) node))
                    (throw (ex-info "Retention reverse index has no edge" {:id (a node n-id)})))))))

(defn- audit-derived-state! [rt]
  (audit-retention! rt)
  (when-not (zero? (count! empty-members))
    (throw (ex-info "Shared empty membership was mutated" {})))
  #?(:cljs
     (let [heap (runtime-field rt :ready)]
       (dotimes [index (.-length heap)]
         (when (pos? index)
           (let [parent (unsigned-bit-shift-right (dec index) 1)]
             (when (> (a (aget heap parent) n-rank) (a (aget heap index) n-rank))
               (throw (ex-info "Ready heap priority changed while queued" {:index index}))))))))
  (let [nodes (vec (values (runtime-field rt :nodes)))
        sources (members)]
    (doseq [node nodes]
      (add! sources node)
      (when-let [source (a node n-creator-source)] (add! sources source)))
    (each! [source sources]
           (let [expected (frequencies
                           (for [node nodes :when (identical? source (a node n-creator-source))
                                 :let [creator (a node n-creator)]]
                             (if (vector? creator) (nth creator 1) (a creator r-gen))))
                 actual (map-value (a source n-creator-refs))]
             (when-not (= expected actual)
               (throw (ex-info "Creator-generation count mismatch" {:entity (a source n-id) :expected expected :actual actual}))))))

  (each! [node (values (runtime-field rt :nodes))]
         (let [current-active (boolean (active-status? (some-> (current node) (a r-status))))
               any-active (boolean (any! (values (a node n-runs)) #(active-status? (a % r-status))))]
           (when-not (= current-active any-active)
             (throw (ex-info "Active-run projection mismatch" {:entity (a node n-id)})))))
  (each! [run (a (runtime-field rt :counters) 6)]
         (let [actual (count (filter #(reactive-kind? (a % o-kind)) (items (a run r-obs))))]
           (when-not (= actual (or (a run r-reactives) 0))
             (throw (ex-info "Reactive-site count mismatch" {:run (a run r-gen) :expected actual :actual (a run r-reactives)}))))))

(defn- boundary-body! [rt action]
  (reclaim! rt)
  (when (prune-timer-queue! rt) (reclaim! rt))
  (prune-ancestry! rt)
  (refresh-custody-releases! rt)
  (refresh-release! rt)
  (custody-release-data! rt)
  (when-let [audit (runtime-field rt :audit)]
    (audit-derived-state! rt)
    (let [pending (a (runtime-field rt :counters) 9)
          ;; A nil trace keeps structural auditing without retaining worlds.
          recording? (some? @audit)
          action (when recording?
                   (let [action (assoc action :fresh-runs (vec (items pending)))]
                     (if-let [operation (when (#{:cleanup-cell :deferred-request :signal-write :mailbox-post-request :mailbox-take-now} (:t action))
                                          (active-operation))]
                       (assoc (dissoc action :th) :op (a operation p-id)
                              :frame (a (current-activation) 11))
                       (if-let [receipt (when (#{:cleanup-cell :deferred-request :signal-write :mailbox-post-request :mailbox-take-now :mailbox-take} (:t action))
                                          (active-mailbox-callback))]
                         (assoc (dissoc action :th) :callback (a receipt x-id)
                                :frame (a (current-activation) 11))
                         action))))]
      #?(:clj (.clear ^java.util.ArrayDeque pending) :cljs (.clear pending))
      (when recording?
        (swap! audit conj [action (snapshot rt) (custody-audit-family rt)]))))
  (retry-cell-gc! rt)
  (refresh-custody! rt))

(defn- boundary! [rt action]
  ;; The current action may join/revoke this facade during maintenance. Borrow
  ;; its actual family for this stack frame so the audit includes THIS action's
  ;; physical census, not the preceding boundary. Late receipt-only actions
  ;; have no active service and keep their separate data-history projection.
  (if *custody-frame*
    (boundary-body! rt action)
    (if-let [service (custody-state rt)]
      (binding [*custody-frame* {:service service :family (:worlds @service)}]
        (boundary-body! rt action))
      (if (and (runtime-field rt :audit) (= :releasing (a (runtime-field rt :lifecycle) 0)))
        (binding [*custody-frame* {:family (runtime-field rt :family)}]
          (boundary-body! rt action))
        (boundary-body! rt action)))))

(defn- touch! [rt node token]
  (when token (add! (a node n-tokens) token) (add! (a token t-touched) (runtime-field rt :world))))
(defn- check-token! [rt token]
  (world-open! rt)
  (when (and token (not (identical? (runtime-field rt :family-id) (a token t-family))))
    (throw (ex-info "Handle belongs to another runtime family" {:error :unknown-handle})))
  (when (and token (has? (a token t-dropped) (runtime-field rt :world)))
    (throw (ex-info "Idle cache released" {:error :idle-cache-released}))))

(defn- check-running! [run]
  (when (active-mailbox-callback)
    (throw (ex-info "Raw Mailbox callback graph effects require typed admission"
                    {:error :unsupported-operation :operation :mailbox-callback-graph-effect})))
  (when (active-operation)
    (throw (ex-info "Protected operation graph effects require typed parent admission"
                    {:error :unsupported-operation :operation :protected-graph-effect})))
  (when (and run (= :unwinding (a run r-status)))
    (throw (or (when-let [ticket (a run r-exit)] (a ticket 14))
               (ex-info "Cancelled execution slice" {:error :cancelled}))))
  (when (and (nil? run) (when-let [frame (current-activation)] (a frame 8)))
    (throw (ex-info "Cleanup permits retained cell access and protected waits only" {:error :cleanup-only}))))

(defn- admit-native-effect! []
  (when-let [frame (current-activation)]
    (let [caller (a frame 0)]
      (when (runtime-field caller :finalization)
        (locked caller (check-running! (a frame 1)))))))

(defn- check-native-caller! [rt]
  (world-open! rt)
  ;; The target gate is held. Related worlds share it; an independent target
  ;; uses the explicit admission point before acquiring its separate gate.
  (when-let [frame (current-activation)]
    (when (and (runtime-field (a frame 0) :finalization)
               (identical? (runtime-field rt :gate) (runtime-field (a frame 0) :gate)))
      (check-running! (a frame 1)))))

(defn- predecessor-run? [previous caller]
  (when (and previous caller (not (root-owner? previous)) (not (scope-owner? previous)))
    (let [id (if (vector? previous) (nth previous 0) (a (a previous r-node) n-id))
          gen (if (vector? previous) (nth previous 1) (a previous r-gen))]
      (and (= id (a (a caller r-node) n-id)) (has? (a caller r-ancestors) gen)))))

(defn- allocate-source! [rt id value]
  (locked rt
          (let [run (when (current-activation) (a (current-activation) 1))
                order (if run (put (current-activation) 2 (inc (long (a (current-activation) 2)))) 0)
                _ (check-running! run)
                owner (selected-owner rt)
                creator (when-not (or (root-owner? owner) (scope-owner? owner)) owner)
                old (find! (runtime-field rt :nodes) id)
                node (or old (node! rt id :signal owner))]
            (when-not (= :signal (a node n-kind)) (throw (ex-info "Source ID collision" {:id id})))
            (when (or (nil? old) (predecessor-run? (a node n-owner) creator))
              (when-not old (put node n-value value))
              (owner! rt node owner) (put node n-order order)
              (when creator (creation! creator node)))
            (boundary! rt (when (runtime-field rt :audit) (cond-> {:t :t02 :w (runtime-field rt :world) :e id :value value}
                                                            creator (assoc :r (run-id creator) :order order)
                                                            (scope-owner? owner) (assoc :scope (owner-id owner) :order order))))
            (->Source id (runtime-field rt :family-id)
                      (when-let [profile (runtime-field rt :finalization)]
                        (or (find! (a profile 3) id)
                            (let [allocation #?(:clj (Object.) :cljs (js-obj))]
                              (assoc! (a profile 3) id allocation) allocation)))))))

(defn signal [requested id value]
  (allocate-source! (execution-runtime requested) id value))

#?(:clj (defonce ^:private handle-cleaner (java.lang.ref.Cleaner/create))
   :cljs (defonce ^:private handle-cleaner
           (js/FinalizationRegistry.
            (fn [held]
              (when-let [home (.deref (aget held 0))]
                (collect-home-token! home (aget held 1)))))))

(defn- arm-handle! [rt handle token]
  #?(:clj (let [home-ref (java.lang.ref.WeakReference. (runtime-field rt :home))]
            (put token 5 (.register ^java.lang.ref.Cleaner handle-cleaner handle
                                    (reify Runnable
                                      (run [_] (when-let [home (.get home-ref)]
                                                 (collect-home-token! home token)))))))
     :cljs (.register handle-cleaner handle (array (js/WeakRef. (runtime-field rt :home)) token) token))
  handle)

(defn- collect-home-token! [home token]
  (let [target #?(:clj (locking (:gate home)
                        ;; WeakHashMap's reference queue otherwise drains only
                        ;; on the next lookup, retaining stale token metadata.
                         (.size ^java.util.WeakHashMap (:host-tokens home))
                         (first (remove custody-data-world? (values (:worlds home)))))
                  :cljs (first (remove custody-data-world? (values (:worlds home)))))]
    (when target (collect-token! target token))))

(defn- collect-token! [rt token]
  (locked rt
          (when (a token t-reachable)
            (put token t-reachable false)
            (each! [world (a token t-touched)]
                   (when-let [target (find! (runtime-field rt :family) world)]
                     (when (and (not (custody-data-world? target)) (find! (runtime-field target :nodes) (a token t-spin)))
                       (push! (runtime-field rt :gc) (doto (slots 2) (put 0 target) (put 1 token))))))
            (boundary! rt (when (runtime-field rt :audit) {:t :t16 :tok (a token t-id)
                                                           :notification-order (mapv #(-> (a % 0) :world)
                                                                                     (items (runtime-field rt :gc)))})))
          (loop []
            (when-let [notification (pop! (runtime-field rt :gc))]
              (let [target (a notification 0) dead (a notification 1)]
                (when-let [node (find! (runtime-field target :nodes) (a dead t-spin))]
                  (remove! (a node n-tokens) dead) (mark! target node))
                (boundary! target (when (runtime-field target :audit) {:t :t17 :w (runtime-field target :world) :e (a dead t-spin) :tok (a dead t-id)})))
              (recur)))))

(defn notify-unreachable!
  "Deterministic exercise of the host-finalization handoff for experiments."
  [rt handle]
  (admit-native-effect!)
  (locked rt
          (check-native-caller! rt)
          (when-not (identical? (runtime-field rt :family-id) (a (:token handle) t-family))
            (throw (ex-info "Handle belongs to another runtime family" {:error :unknown-handle})))
          #?(:clj (.clean ^java.lang.ref.Cleaner$Cleanable (a (:token handle) 5))
             :cljs (do (.unregister handle-cleaner (:token handle)) (collect-token! rt (:token handle))))))

(defn- new-token [rt id]
  (doto (slots 7)
    (put t-family (runtime-field rt :family-id)) (put t-id (random-uuid))
    (put t-spin id) (put t-reachable true)
    (put t-touched (members)) (put t-dropped (members))))

(defn- construct-token!
  ([rt id token run] (construct-token! rt id token run true))
  ([rt id token run construction?]
   (world-open! rt)
   (check-running! run)
   (let [owner (if construction? (selected-owner rt) (runtime-field rt :owner-root))
         creator (when-not (or (root-owner? owner) (scope-owner? owner)) owner)]
     (when-let [node (find! (runtime-field rt :nodes) id)]
       (when-not (= :spin (a node n-kind))
         (throw (ex-info "Computation ID collision" {:id id}))))
     (when (runtime-field rt :tokens) (add! (runtime-field rt :tokens) token))
     (let [order (if run (put (current-activation) 2 (inc (long (a (current-activation) 2)))) 0)
           node (find! (runtime-field rt :nodes) id)]
       (when (and creator (nil? node))
         (let [node (node! rt id :spin creator)]
           (creator! rt node creator) (kept! rt node (reactive? creator)) (put node n-order order)
           (creation! creator node)))
       (when-let [node (find! (runtime-field rt :nodes) id)]
         (when (predecessor-run? (a node n-creator) creator)
           (adopt! rt node creator)
           (owner! rt node creator) (creator! rt node creator) (kept! rt node (reactive? creator))
           (put node n-order order) (creation! creator node))
         (touch! rt node token))
       (boundary! rt (when (runtime-field rt :audit)
                       (cond-> {:t :t01 :w (runtime-field rt :world) :e id :tok (a token t-id)}
                         creator (assoc :r (run-id creator) :order order)
                         (scope-owner? owner) (assoc :scope (owner-id owner)))))))))

(defn make-spin [requested id body]
  (let [rt (execution-runtime requested)
        token (locked rt
                      (world-open! rt)
                      (let [token (new-token rt id)]
                        (construct-token! rt id token (when (current-activation) (a (current-activation) 1)))
                        token))]
    (arm-handle! rt (->Handle id token body) token)))

(defn- portable-token! [rt target id construction?]
  ;; Only the engine's identity-equality public Spin objects enter this cache.
  ;; Values contain no body, public target or strong reference to the family.
  (locked rt
          (world-open! rt)
          (selected-owner rt)
          (when (and (current-activation) (identical? (runtime-field rt :owner-root)
                                                      (runtime-field (a (current-activation) 0) :owner-root)))
            (check-running! (a (current-activation) 1)))
          (let [cache (:host-tokens (runtime-field rt :home))]
            (or #?(:clj (.get ^java.util.WeakHashMap cache target) :cljs (.get cache target))
                (let [token (new-token rt id)]
                  ;; First use in another family is not body construction:
                  ;; an existing portable host handle must not acquire a creator.
                  (construct-token! rt id token (when (and construction? (current-activation)
                                                           (identical? (runtime-field rt :owner-root)
                                                                       (runtime-field (a (current-activation) 0) :owner-root)))
                                                  (a (current-activation) 1)) construction?)
                  (arm-handle! rt target token)
                  #?(:clj (.put ^java.util.WeakHashMap cache target token) :cljs (.set cache target token))
                  token)))))

(defn- admit-world-switch! [rt]
  ;; An explicit request into another world is a host-root request there.
  ;; Validate the initiating slice under its OWN gate before acquiring the
  ;; destination gate. This is its caller-admission point: later cancellation
  ;; does not retract an already admitted request into an independent world.
  ;; Never read a foreign run's mutable status under the destination gate.
  (when-let [frame (current-activation)]
    (let [caller (a frame 0)]
      (when (and (active-operation)
                 (not (identical? (runtime-field caller :owner-root) (runtime-field rt :owner-root))))
        (throw (ex-info "Protected operation cannot switch worlds" {:error :cleanup-only})))
      (when-not (identical? (runtime-field caller :owner-root) (runtime-field rt :owner-root))
        (locked caller (check-running! (a frame 1)))))))

(defn register-computation!
  "Record construction of a portable public computation in this family.
  The target must have Object identity equality (the public Spin deftype)."
  ([requested target id]
   (try
     (admit-world-switch! requested)
     (portable-token! (canonical-runtime requested) target id true)
     nil
     (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))
  ([requested target id body]
   (try
     (admit-world-switch! requested)
     (let [rt (canonical-runtime requested)
           token (portable-token! rt target id true)]
       (prepare-computation! rt id body true token))
     nil
     (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil)))))

(defn track [& _] (throw (ex-info "track requires cspin" {})))
(defn await [& _] (throw (ex-info "await requires cspin" {})))
(defn park [& _] (throw (ex-info "park requires cspin" {})))
(defn await-finalization [& _] (throw (ex-info "await-finalization requires cspin" {})))
(defn await-host [& _] (throw (ex-info "await-host requires cspin" {})))
(defn ticket [id] (->Ticket id))
#?(:clj
   (do
     (defn- binding-sites [form vars]
       (cond
         (seq? form)
         (let [[op bindings & body] form]
           (cond
             (or (= 'quote op) (and (symbol? op) (= "cspin" (name op)))) form
             (#{'binding 'clojure.core/binding 'cljs.core/binding} op)
             (with-meta (list* op bindings (map #(binding-sites % (vec (distinct (concat vars (take-nth 2 bindings))))) body))
               (meta form))
             :else (with-meta (apply list (map #(binding-sites % vars) form))
                 ;; CLJS emits runtime metadata on fn expressions. Binding
                 ;; annotations belong to effect calls, never function values.
                     (cond-> (meta form)
                       (and (seq vars) (not (#{'fn 'fn* 'clojure.core/fn 'cljs.core/fn} (first form))))
                       (assoc ::binding-vars vars)))))
         (vector? form) (with-meta (mapv #(binding-sites % vars) form) (meta form))
         (map? form) (with-meta (into {} (map (fn [[k v]] [(binding-sites k vars) (binding-sites v vars)])) form) (meta form))
         :else form))
     (defn- bound-resume-form [vars k env]
       (let [ordinary (vec (remove #(contains? @ioc/binding-scopes (ioc/var-name env %)) vars))
             saved (mapv #(gensym (str (name %) "-saved")) ordinary)]
         `(let [~@(interleave saved ordinary)
                scoped-k# (cps-runtime/scope-continuation ~k)]
            (fn [value#]
              (binding [~@(interleave ordinary saved)]
                ;; The pump must stay inside the restored user scope. Direct
                ;; inline returns use raw continuations, so this is one frame
                ;; per resumed slice, never one nested frame per loop bounce.
                (cps/with-trampoline (cps/invoke-continuation scoped-k# value#)))))))
     (defn- breakpoint [handler inline? ctx r e]
       (fn [args]
         (let [vars (::binding-vars (meta (:form ctx)))]
           (if (seq vars)
             (if inline?
               `(~handler ~@args ~r ~e ~(bound-resume-form vars r (:env ctx)) ~(bound-resume-form vars e (:env ctx)))
               `(~handler ~@args ~(bound-resume-form vars r (:env ctx)) ~(bound-resume-form vars e (:env ctx))))
             `(~handler ~@args ~r ~e)))))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-track [ctx r e] (breakpoint `track-effect! true ctx r e))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-await [ctx r e] (breakpoint `await-effect! true ctx r e))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-park [ctx r e] (breakpoint `park-effect! false ctx r e))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-finalization [ctx r e] (breakpoint `await-finalization-effect! true ctx r e))
     (defn ^:is.simm.partial-cps.ioc/eager-arguments bp-await-host [ctx r e] (breakpoint `await-host-effect! false ctx r e))
     (defmacro cspin [rt id & body]
       `(make-spin ~rt ~id ~((requiring-resolve 'org.replikativ.spindel.spin.cps/build-cps-fn)
                             (map #(binding-sites % []) body)
                             (merge cps/breakpoints
                                    {'org.replikativ.spindel.engine.impl.owned/track
                                     'org.replikativ.spindel.engine.impl.owned/bp-track
                                     'org.replikativ.spindel.engine.impl.owned/await
                                     'org.replikativ.spindel.engine.impl.owned/bp-await
                                     'org.replikativ.spindel.engine.impl.owned/park
                                     'org.replikativ.spindel.engine.impl.owned/bp-park
                                     'org.replikativ.spindel.engine.impl.owned/await-host
                                     'org.replikativ.spindel.engine.impl.owned/bp-await-host
                                     'org.replikativ.spindel.engine.impl.owned/await-finalization
                                     'org.replikativ.spindel.engine.impl.owned/bp-finalization}) &env)))))

(defn- ready-add! [rt node]
  #?(:clj (.add ^java.util.PriorityQueue (runtime-field rt :ready) node)
     :cljs (let [heap (runtime-field rt :ready) index (.-length heap) rank (a node n-rank)]
             (.push heap node)
             (loop [index index]
               (if (pos? index)
                 (let [parent (unsigned-bit-shift-right (dec index) 1)
                       above (aget heap parent)]
                   (if (> (a above n-rank) rank)
                     (do (aset heap index above) (recur parent))
                     (aset heap index node)))
                 (aset heap index node))))))

(defn- schedule! [rt node ob]
  (put node n-pending-generation (a (current node) r-gen))
  (let [previous (a node n-resume)]
    (when (or (nil? previous) (and ob (< (long (a ob o-order)) (long (a previous o-order)))))
      (put node n-resume ob)))
  (when-not (a node n-ready)
    (put node n-ready true)
    (ready-add! rt node)))

(defn- run-slots! [rt]
  (or (pop! (a (runtime-field rt :counters) 0))
      (let [run (slots 26)]
        (fields! [field [r-created r-spawned r-obs r-owned r-backlinks r-childruns r-ancestors]]
                 (put run field empty-members))
        run)))

(defn- start! [rt node owner reentry?]
  (when-not (= :spin (a node n-kind))
    (throw (ex-info "Only computations have executable runs" {:error :not-computation :id (a node n-id)})))
  (when-not reentry? (put node n-resume nil))
  (each-copy! [inherited (values (a node n-runs))]
              (when (= :inherited (a inherited r-status)) (cancel! rt inherited)))
  (put node n-cancelled nil)
  (let [run (run-slots! rt)
        pred (current node)
        generation (put (runtime-field rt :serial) 1 (inc (long (a (runtime-field rt :serial) 1))))]
    (put node n-generation generation)
    (when (runtime-field rt :audit)
      (assoc! (a (runtime-field rt :counters) 3) (a node n-id) generation)
      (push! (a (runtime-field rt :counters) 9) [(runtime-field rt :world) (a node n-id) generation]))
    (put run r-reactives 0) (put run r-validation-lost nil)
    (when (and pred (not= :unwinding (a pred r-status)))
      (each! [gen (a pred r-ancestors)] (add-run! run r-ancestors gen))
      (add-run! run r-ancestors (a pred r-gen)))
    (put run r-node node) (put run r-gen generation) (put run r-owner owner)
    (put run r-pred (when (and pred (not= :unwinding (a pred r-status))) (a pred r-gen))) (put run r-status :running)
    (put run r-seq (put (runtime-field rt :counters) 1 (inc (max (long (a (runtime-field rt :counters) 1)) (long (a (runtime-field rt :counters) 2))))))
    (assoc! (a node n-runs) generation run)
    (add! (a (runtime-field rt :counters) 6) run)
    (put node n-current run)
    (when-not (root-owner? owner)
      (if (scope-owner? owner)
        (add! (a (owner-storage owner) s-runs) run)
        (do (add-run! owner r-spawned run) (add-run! run r-backlinks owner)
            (add-run! owner r-childruns run)))
      (when-let [parent (owner-node owner)]
        (mark! rt parent)
        (when-not (has? (a node n-links) parent) (mark-graph! rt node))))
    (schedule! rt node nil)
    (mark! rt node) run))

(defn- ob! [rt kind debtor run order resolve reject]
  (let [ob (slots 24) id (a (runtime-field rt :serial) 0)]
    (next-number! rt 0)
    (put ob o-address (when run (a run r-address)))
    (put ob o-id id) (put ob o-kind kind) (put ob o-debtor debtor) (put ob o-run run)
    (when run (put ob o-creditor-generation (a run r-gen)) (put ob o-creditor-node (a run r-node)))
    (put ob o-standing (case kind (:track :await-reactive :callback) true false))
    (put ob o-resolve resolve) (put ob o-reject reject) (put ob o-order order)
    (put ob o-slot (if (= kind :track) :consumed :armed)) (put ob o-live true)
    (when (= :await-once kind) (assoc! (runtime-field rt :deliveries) id ob))
    (when run (add-run! run r-obs ob) (mark! rt (a run r-node))
          (when (and debtor (not (has? (a (a run r-node) n-links) debtor)))
            (mark-graph! rt (a run r-node)))
          (when (reactive-kind? kind) (reactive-delta! run 1)))
    (when debtor
      (add! (a debtor n-dependents) ob) (mark! rt debtor)
      (when (and (nil? run) (not (a debtor n-external-root))) (mark-graph! rt debtor)))
    ob))

(defn- adopt! [rt node caller]
  (let [previous (a node n-owner)]
    (when (predecessor-run? previous caller)
      (when (identical? previous (a node n-creator))
        (creator! rt node caller) (kept! rt node (reactive? caller))
        (creation! caller node))
      (owner! rt node caller)
      (each! [run (values (a node n-runs))]
             (when (identical? previous (a run r-owner))
               (remove! (a previous r-childruns) run) (put run r-owner caller) (add-run! caller r-childruns run))))))

(defn- rank! [run debtor]
  (when debtor
    (let [node (a run r-node) rank (inc (long (a debtor n-rank)))]
      (when (> rank (long (a node n-rank)))
        ;; Both platform queues borrow node priorities. Rank is refined only
        ;; after claiming a slice, never while its node remains queued.
        (when (and (runtime-field (a node n-runtime) :audit) (a node n-ready))
          (throw (ex-info "Queued priority mutation" {:id (a node n-id)})))
        (put node n-rank rank)))))

(defn- public-track-interval! [node ob first?]
  (when-let [aux (a node n-public-signal)]
    (let [packet (a aux 0) generation (:generation packet)
          consumed (a ob o-signal-generation)
          value (a node n-value)]
      (put ob o-signal-generation generation)
      (if (or first? (nil? consumed) (> generation consumed))
        (iv/->Interval (:old-snapshot packet) value (:deltas packet))
        (iv/->Interval value value nil)))))

(defn- register-track!
  ([rt run order id resolve reject] (register-track! rt run order id resolve reject nil))
  ([rt run order id resolve reject expected-source]
   (locked rt
           (check-running! run)
           (let [node (or (find! (runtime-field rt :nodes) id)
                          (throw (ex-info "Foreign or released track is outside this slice" {:id id})))
                 _ (when (#{:deferred :mailbox} (a node n-kind))
                     (throw (ex-info "Deferred permits one-shot await only" {:error :unsupported-deferred-obligation})))
                 _ (when expected-source (public-signal-view! rt expected-source))
                 ob (ob! rt :track node run order resolve reject)]
             (put ob o-last (a node n-value)) (rank! run node)
             (put (current-activation) 9 nil)
             (when (a node n-public-signal)
               (put (current-activation) 9 (public-track-interval! node ob true)))
             (boundary! rt (when (runtime-field rt :audit) {:t :t05 :w (runtime-field rt :world) :r [(a (a run r-node) n-id) (a run r-gen)]
                                                            :kind :track :order order :debtor [:entity (runtime-field rt :world) id]}))
             (a node n-value)))))

(defn- track-id-effect!
  ([id resolve reject resume-resolve resume-reject]
   (track-id-effect! id resolve reject resume-resolve resume-reject nil))
  ([id resolve reject resume-resolve resume-reject expected-source]
   (let [frame (current-activation) rt (a frame 0) run (a frame 1)
         order (put frame 2 (inc (long (a frame 2))))
         value (register-track! rt run order id resume-resolve resume-reject expected-source)]
     (cps/invoke-continuation resolve (or (a frame 9) (iv/->Interval value value nil))))))

(defn- check-source! [rt source]
  (when-not (identical? (runtime-field rt :family-id) (:family source))
    (throw (ex-info "Source belongs to another runtime family" {:error :unknown-source}))))

(defn track-effect!
  ([source resolve reject]
   (check-source! (a (current-activation) 0) source)
   (track-id-effect! (:id source) resolve reject resolve reject))
  ([source resolve reject resume-resolve resume-reject]
   (check-source! (a (current-activation) 0) source)
   (track-id-effect! (:id source) resolve reject resume-resolve resume-reject)))

(defn- deliver-value! [resolve reject value failed?]
  (cps/invoke-continuation (if failed? reject resolve) value))
(defn- deliver-cont! [ob value]
  (deliver-value! (a ob o-resolve) (a ob o-reject) value (a ob o-delivery-error)))

(defn- register-await! [rt run order id token body resolve reject descriptor-reference]
  (locked rt
          (check-running! run)
          (check-token! rt token)
          (when (and (nil? (find! (runtime-field rt :nodes) id)) (parent-node rt id))
            (throw (ex-info "Foreign await is outside this slice" {:id id})))
          (let [owner (selected-owner rt)
                node (or (find! (runtime-field rt :nodes) id) (node! rt id :spin owner))]
            (when-not (= :spin (a node n-kind))
              (throw (ex-info "Computation await target has another kind" {:error :not-computation :id id})))
            (when-not (or (scope-owner? owner) (root-owner? owner)) (adopt! rt node owner))
            (when-not (a node n-owner) (owner! rt node owner))
            (when (and (not (work-status? (some-> (current node) (a r-status))))
                       (or (not (a node n-complete)) (a node n-dirty)))
              ;; A checkpoint may select its saved executable on a genuine
              ;; cold restart. Seat the matching descriptor proof with it;
              ;; valid caches and already-running generations keep their own
              ;; template, scope and descriptor instead.
              (put node n-body body)
              (put node n-descriptor descriptor-reference)
              (start! rt node owner false))
            (let [ob (ob! rt :await-reactive node run order resolve reject)]
              ;; A resumed await rechecks this exact call template. Its
              ;; debtor's ordinary cache may be released before the queued
              ;; continuation claims a slice, including its n-body field.
              (put ob o-body body)
              (put run r-status :parked) (when (runtime-field rt :finalization) (put run r-cancel-cont reject)) (touch! rt node token) (rank! run node)
              (let [ready? (and (a node n-complete) (not (a node n-dirty))
                                (not (work-status? (some-> (current node) (a r-status)))))]
                ;; T5+T6 share the gate and run no user code between them. Both
                ;; statuses retain the same standing obligation and ownership;
                ;; one final Rule L closure suffices. Audit mode still exposes
                ;; both model states for the independent transition replay.
                (when (or (not ready?) (runtime-field rt :audit))
                  (boundary! rt (when (runtime-field rt :audit) (cond-> {:t :t05 :w (runtime-field rt :world) :r [(a (a run r-node) n-id) (a run r-gen)]
                                                                         :kind :await-reactive :order order :debtor [:entity (runtime-field rt :world) id]}
                                                                  token (assoc :tok (a token t-id))))))
                (when ready?
                  (put ob o-slot :consumed) (put run r-status :running) (put ob o-value (a node n-value))
                  (put ob o-delivery-error (= :error (a node n-complete)))
                  (boundary! rt (when (runtime-field rt :audit) {:t :t06 :w (runtime-field rt :world) :o [:o (a ob o-id)] :value (diagnostic-value (a node n-value) (a ob o-delivery-error))}))))
              ob))))

(defn- await-id-effect! [id token body resolve reject resume-resolve resume-reject]
  (let [frame (current-activation) rt (a frame 0) run (a frame 1)
        order (put frame 2 (inc (long (a frame 2))))
        descriptor-reference (weak-descriptor (::rtp/computation (meta body)))
        ob (register-await! rt run order id token body resume-resolve resume-reject descriptor-reference)]
    (when (= :consumed (a ob o-slot)) (deliver-value! resolve reject (a ob o-value) (a ob o-delivery-error)))))

(defn await-effect!
  ([source resolve reject]
   (try
     (await-id-effect! (:id source) (:token source) (:body source) resolve reject resolve reject)
     (finally #?(:clj (java.lang.ref.Reference/reachabilityFence source) :cljs nil))))
  ([source resolve reject resume-resolve resume-reject]
   (try
     (await-id-effect! (:id source) (:token source) (:body source) resolve reject resume-resolve resume-reject)
     (finally #?(:clj (java.lang.ref.Reference/reachabilityFence source) :cljs nil)))))

(defn await-computation-effect!
  "Typed public await handoff; no family-bound Handle wrapper is allocated."
  [target id body resolve reject]
  (try
    (let [rt (a (current-activation) 0)]
      (locked rt
              (check-running! (a (current-activation) 1))
              (when (and (nil? (find! (runtime-field rt :nodes) id)) (parent-node rt id))
                (throw (ex-info "Foreign await is outside this slice" {:id id}))))
      (await-id-effect! id (portable-token! rt target id false) body resolve reject resolve reject))
    (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))

(defn park-effect! [ticket resolve reject]
  (let [rt (a (current-activation) 0) run (a (current-activation) 1)
        order (put (current-activation) 2 (inc (long (a (current-activation) 2))))]
    (locked rt
            (check-running! run)
            (let [ob (ob! rt :await-once nil run order resolve reject)
                  waiters (or (find! (runtime-field rt :tickets) (:id ticket))
                              (assoc! (runtime-field rt :tickets) (:id ticket) (members)))]
              (put ob o-host (:id ticket)) (add! waiters ob)
              (put run r-status :parked) (when (runtime-field rt :finalization) (put run r-cancel-cont reject))
              (boundary! rt (when (runtime-field rt :audit) {:t :t05 :w (runtime-field rt :world) :r [(a (a run r-node) n-id) (a run r-gen)]
                                                             :kind :await-once :order order :debtor [:host (:id ticket)]}))))))

(defn pending-ticket [requested ticket]
  (let [rt (execution-runtime requested)]
    (locked rt
            (when-let [waiters (find! (runtime-field rt :tickets) (:id ticket))]
              (when-let [ob (first (items waiters))]
                (->Delivery (runtime-field rt :family-id) (runtime-field rt :world) (a ob o-id)))))))

(defn- settle-ticket! [requested delivery value failed?]
  (admit-native-effect!)
  (let [rt (execution-runtime requested)]
    (when-not (and (identical? (runtime-field rt :family-id) (:family delivery)) (= (runtime-field rt :world) (:world delivery)))
      (throw (ex-info "Delivery belongs to a different runtime family or world" {:world (:world delivery)})))
    (locked rt
            (check-native-caller! rt)
            (when (find! (a (runtime-field rt :timers) 0)
                         [:timer (runtime-field rt :world) [:o (:obligation delivery)]])
              (throw (ex-info "Timer readiness requires its registered callback"
                              {:error :unsupported-operation :operation :timer-delivery})))
            (when-let [ob (find! (runtime-field rt :deliveries) (:obligation delivery))]
              (let [run (a ob o-run)]
                (when (and (= :armed (a ob o-slot)) (resumable-status? (a run r-status)))
                  (end-ob! rt ob) (put run r-status :running) (put ob o-value value)
                  (put ob o-delivery-error failed?)
                  (schedule! rt (a run r-node) ob))))
            (boundary! rt (when (runtime-field rt :audit) {:t :t06 :w (runtime-field rt :world)
                                                           :o [:o (:obligation delivery)]
                                                           :value (diagnostic-value value failed?)})))
    (drain! rt)))

(defn resume-ticket! [requested delivery value]
  (settle-ticket! requested delivery value false))

(defn reject-ticket! [requested delivery error]
  (settle-ticket! requested delivery error true))

(defn- deliver-host! [rt delivery value failed?]
  ;; A native callback owns this exact world/registration. In particular, a
  ;; synchronous callback must not redirect through some other active world.
  (locked rt
          (when-let [ob (find! (runtime-field rt :deliveries) (:obligation delivery))]
            (let [run (a ob o-run)]
              (when (and (= :armed (a ob o-slot)) (resumable-status? (a run r-status)))
                (put ob o-slot :consumed)
                (end-ob! rt ob) (put run r-status :running) (put ob o-value value)
                (put ob o-delivery-error failed?)
                (schedule! rt (a run r-node) ob))))
          (boundary! rt (when (runtime-field rt :audit) {:t :t06 :w (runtime-field rt :world)
                                                         :o [:o (:obligation delivery)]
                                                         :value (diagnostic-value value failed?)})))
  (drain! rt))

(defn- host-callback [rt delivery failed?]
  ;; A producer may keep a callback after cancellation/completion. That stale
  ;; capability must not keep the entire world and its application heap alive.
  (let [weak #?(:clj (java.lang.ref.WeakReference. rt) :cljs (js/WeakRef. rt))]
    (fn [value]
      (when-let [target #?(:clj (.get weak) :cljs (.deref weak))]
        (deliver-host! target delivery value failed?)))))

(defn await-host-effect!
  "Park on a one-shot callback registration. `start` runs outside the gate with
  success/error callbacks and returns an optional cancellation function.
  Delivery is once-only and world/run fenced; cancellation is post-commit.
  Cancellation must synchronously detach the registration. Physical resources
  requiring asynchronous join need a separate lifetime owner/acknowledgement.
  Registrations require recovery support before they can be forked."
  [start resolve reject]
  (let [frame (current-activation) rt (a frame 0) run (a frame 1)
        order (put frame 2 (inc (long (a frame 2))))
        operation (slots 2)
        delivery (locked rt
                         (check-running! run)
                         (let [ob (ob! rt :await-once nil run order resolve reject)
                               host [:native (a ob o-id)]]
                           (put operation 0 :starting)
                           (assoc! (runtime-field rt :operations) (a ob o-id) operation)
                           (put ob o-host host) (put run r-status :parked) (when (runtime-field rt :finalization) (put run r-cancel-cont reject))
                           (boundary! rt (when (runtime-field rt :audit) {:t :t05 :w (runtime-field rt :world)
                                                                          :r [(a (a run r-node) n-id) (a run r-gen)]
                                                                          :kind :await-once :order order :debtor [:host host]}))
                           (->Delivery (runtime-field rt :family-id) (runtime-field rt :world) (a ob o-id))))]
    (when (locked rt (= :starting (a operation 0)))
      (let [cancel (try
                     (start (host-callback rt delivery false) (host-callback rt delivery true))
                     (catch #?(:clj Throwable :cljs :default) error
                       (deliver-host! rt delivery error true)
                       nil))]
        (locked rt
                (case (a operation 0)
                  :starting (do (put operation 0 :live) (put operation 1 cancel))
                  :cancelled (when cancel (push! (runtime-field rt :posts) (doto (slots 1) (put 0 cancel))))
                  :settled nil))))
    nil))

(defn- timer-row [rt timer]
  (let [run (a timer z-run)]
    (cond-> {:kind :timer-resource :owner [(runtime-field rt :world) (run-id run)]
             :state :running :o [:o (a timer 11)] :order (a timer z-order) :delay-ms (a timer z-delay)
             :phase (a timer z-phase) :install (a timer z-install) :handle (a timer z-handle-state)
             :frames (a timer z-frames) :installer :engine
             :retired? (= :unwinding (a run r-status))
             :anchor (or (a run r-anchor) (run-anchor rt run))}
      (= :armed (a timer z-phase)) (assoc :value (a timer z-value)))))

(defn- timer-profile-view [rt]
  (let [profile (profile-view rt) timers (a (runtime-field rt :timers) 0)]
    (if (empty-dict? timers) profile
        (update (or profile {}) :native merge
                (into {} (for [timer (values timers)] [(a timer z-id) (timer-row rt timer)]))))))

(defn- timer-action [rt timer kind]
  {:t kind :w (runtime-field rt :world) :n (a timer z-id)})

(defn- timer-prune! [rt timer]
  (when (and (not= :armed (a timer z-phase)) (not= :pending (a timer z-install))
             (empty? (a timer z-frames)) (#{:none :released :failed} (a timer z-handle-state))
             (identical? timer (find! (a (runtime-field rt :timers) 0) (a timer z-id))))
    (let [run (a timer z-run) ticket (a run r-exit)]
      (dissoc! (a (runtime-field rt :timers) 0) (a timer z-id))
      (put run r-timers (dec (long (a run r-timers))))
      (put timer z-run nil) (put timer z-ob nil) (put timer z-value nil) (put timer z-handle nil)
      (when (and (zero? (long (a run r-timers))) (= :unwinding (a run r-status))
                 (not (a run r-physical))
                 (or (nil? ticket) (nil? (find! (a (runtime-field rt :finalization) 0) (a ticket x-id)))))
        (forget-run! rt run)))))

(defn- prune-timer-queue! [rt]
  (loop [changed? false]
    (if-let [timer (pop! (a (runtime-field rt :timers) 2))]
      (do (timer-prune! rt timer) (recur true))
      changed?)))

(defn- release-timer-handle! [rt timer]
  (let [handle (locked rt
                       (when (= :release-pending (a timer z-handle-state))
                         (put timer z-handle-state :release-claimed)
                         (boundary! rt (when (runtime-field rt :audit)
                                         (assoc (timer-action rt timer :timer-handle-release) :phase :claim)))
                         [(a timer z-handle)]))]
    (when handle
      (let [failure (try
                      (timer-transport/cancel-native-timer! (a (runtime-field rt :timers) 1) (first handle))
                      nil
                      (catch #?(:clj Throwable :cljs :default) error [error]))]
        (locked rt
                (put timer z-handle nil)
                (put timer z-handle-state (if failure :failed :released))
                (timer-prune! rt timer)
                (boundary! rt (when (runtime-field rt :audit)
                                (cond-> (assoc (timer-action rt timer :timer-handle-release)
                                               :phase :returned :variant (if failure :error :ok))
                                  failure (assoc :value (diagnostic-value (first failure) true))))))
        (when failure
          (fault/report-fault! ::fault/executor-task-fault
                               {:error (first failure) :site :native-timer-release}))))))

(defn- queue-timer-release! [rt timer]
  (when (= :present (a timer z-handle-state))
    (put timer z-handle-state :release-pending)
    (push! (runtime-field rt :posts) (doto (slots 1) (put 0 #(release-timer-handle! rt timer))))))

(defn- timer-revoke! [rt timer]
  ;; Called inside the same obligation-retirement transaction. A fired timer
  ;; already closed entry and must not be reclassified as revoked.
  (when (= :armed (a timer z-phase))
    (put timer z-phase :revoked) (put timer z-value nil) (put timer z-ob nil)
    (queue-timer-release! rt timer)
    (push! (a (runtime-field rt :timers) 2) timer)))

(defn- settle-timer! [rt timer value failed?]
  (let [ob (a timer z-ob) run (a timer z-run)]
    (put timer z-phase (if failed? :failed :fired))
    (put timer z-value nil)
    (put ob o-slot :consumed)
    (end-ob! rt ob)
    (put timer z-ob nil)
    (put ob o-value value) (put ob o-delivery-error failed?)
    (put run r-status :running)
    (schedule! rt (a run r-node) ob)
    (queue-timer-release! rt timer)))

(defn- fire-timer! [rt id error failed?]
  (let [claimed (locked rt
                        (when-let [timer (find! (a (runtime-field rt :timers) 0) id)]
                          (let [run (a timer z-run) ob (a timer z-ob)]
                            (when (and (= :armed (a timer z-phase)) ob (a ob o-live)
                                       (= :armed (a ob o-slot)) (= :parked (a run r-status))
                                       (identical? run (current (a run r-node))))
                              (let [frame [:timer-frame id 0]
                                    value (if failed? error (a timer z-value))]
                                (put timer z-frames #{frame})
                                (settle-timer! rt timer value failed?)
                                (boundary! rt (when (runtime-field rt :audit)
                                                (assoc (timer-action rt timer :timer-fire)
                                                       :frame frame :variant (if failed? :error :ok)
                                                       :value (diagnostic-value value failed?))))
                                [timer frame])))))]
    (when claimed
      (let [[timer frame] claimed]
        (try
          ;; During synchronous installation the enclosing ordinary drain is
          ;; already active. Readiness queues work; it cannot resume it inline.
          (drain! rt)
          (finally
            (locked rt
                    (put timer z-frames (disj (a timer z-frames) frame))
                    (timer-prune! rt timer)
                    (boundary! rt (when (runtime-field rt :audit)
                                    (assoc (timer-action rt timer :timer-return) :frame frame))))))))))

(defn- timer-callback [rt id failed?]
  ;; Keep this factory separate from installer closures: a JS shared lexical
  ;; environment must not retain the run, body, value or continuations.
  (let [weak #?(:clj (java.lang.ref.WeakReference. rt) :cljs (js/WeakRef. rt))]
    (if failed?
      (fn [error]
        (when-let [target #?(:clj (.get weak) :cljs (.deref weak))]
          (fire-timer! target id error true)))
      (fn []
        (when-let [target #?(:clj (.get weak) :cljs (.deref weak))]
          (fire-timer! target id nil false))))))

(defn await-public-timer! [requested delay-ms value resolve reject]
  (when (or (active-operation) (active-mailbox-callback))
    (throw (ex-info "Timer waits require ordinary execution admission"
                    {:error :cleanup-only :operation :timer-wait})))
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) frame (current-activation)]
    (when-not (and frame (same-cell-world? rt (a frame 0)) (a frame 1))
      (throw (ex-info "Timer wait requires an ordinary computation" {:error :unsupported-operation :operation :timer-wait})))
    ;; check-running! rejects operation/raw frames before any registration.
    (locked rt (check-running! (a frame 1)))
    (when-not (number? delay-ms)
      (throw (ex-info "Timer delay must be numeric" {:error :invalid-timer-delay :delay-ms delay-ms})))
    (let [resolve (cps-runtime/scope-continuation resolve) reject (cps-runtime/scope-continuation reject)
          timer (locked rt
                        (let [run (a frame 1)]
                          (check-running! run)
                          (custody-resource-ingress! rt)
                          (when-not (and (a run r-physical) (= :running (a run r-status))
                                         (identical? run (current (a run r-node))))
                            (throw (ex-info "Timer installer is not current" {:error :cancelled})))
                          (let [order (put frame 2 (inc (long (a frame 2))))
                                ob (ob! rt :timer nil run order resolve reject)
                                id [:timer (runtime-field rt :world) [:o (a ob o-id)]]
                                timer (doto (slots 12)
                                        (put z-id id) (put z-run run) (put z-ob ob) (put 11 (a ob o-id))
                                        (put z-order order) (put z-delay delay-ms) (put z-value value)
                                        (put z-phase :armed) (put z-install :pending) (put z-handle-state :none)
                                        (put z-frames #{}))]
                            (put ob o-timer timer) (put ob o-host :executor)
                            (put run r-timers (inc (long (or (a run r-timers) 0))))
                            (put run r-status :parked)
                            (when (runtime-field rt :finalization) (put run r-cancel-cont reject))
                            (assoc! (a (runtime-field rt :timers) 0) id timer)
                            (boundary! rt (when (runtime-field rt :audit)
                                            {:t :timer-register :w (runtime-field rt :world) :r (run-id run)
                                             :o [:o (a ob o-id)] :n id :order order :delay-ms delay-ms :value value :th :engine}))
                            timer)))
          outcome (try
                    [:ok (timer-transport/schedule-native-timer!
                          (a (runtime-field rt :timers) 1) delay-ms
                          (timer-callback rt (a timer z-id) false) (timer-callback rt (a timer z-id) true))]
                    (catch #?(:clj Throwable :cljs :default) error [:error error]))
          failed? (= :error (first outcome))
          late-failure? (volatile! false)]
      (locked rt
              (if failed?
                (do (vreset! late-failure? (not= :armed (a timer z-phase)))
                    (put timer z-install :failed)
                    (when (= :armed (a timer z-phase)) (settle-timer! rt timer (second outcome) true)))
                (let [handle (second outcome)]
                  (put timer z-install (if (some? handle) :seated :none))
                  (when (some? handle)
                    (put timer z-handle handle) (put timer z-handle-state :present)
                    (when-not (= :armed (a timer z-phase)) (queue-timer-release! rt timer)))))
              (timer-prune! rt timer)
              (boundary! rt (when (runtime-field rt :audit)
                              (cond-> (assoc (timer-action rt timer :timer-install-result)
                                             :variant (if failed? :error :ok)
                                             :handle? (and (not failed?) (some? (second outcome))))
                                failed? (assoc :value (diagnostic-value (second outcome) true))))))
      (when @late-failure?
        (fault/report-fault! ::fault/executor-task-fault {:error (second outcome) :site :native-timer-install}))
      :org.replikativ.spindel.spin/incomplete)))

(defn- protected-callback [rt id sequence failed?]
  (let [weak #?(:clj (java.lang.ref.WeakReference. rt) :cljs (js/WeakRef. rt))]
    (fn [value]
      (when-let [target #?(:clj (.get weak) :cljs (.deref weak))]
        (locked target
                (when-let [ticket (find! (a (runtime-field target :finalization) 0) id)]
                  (when (and (nil? (a ticket x-operation))
                             (= :waiting (a ticket x-phase)) (= sequence (a ticket x-seq)))
                    (end-deferred-protection! target ticket)
                    (put ticket x-phase :ready) (put ticket x-value value)
                    (put ticket x-failed failed?) (put ticket x-delivered true)
                    (queue-cleanup! target ticket)))
                (boundary! target (when (runtime-field target :audit)
                                    {:t :cleanup-deliver :n id :sequence sequence
                                     :value (diagnostic-value value failed?)})))
        (drain! target)))))

(defn- resume-finalization! [rt ticket]
  (let [run (a ticket x-run)]
    (when (and run (identical? run (current (a run r-node))) (= :parked (a run r-status))
               (= :cps-finalization (a ticket x-kind)) (= :ready (a ticket x-phase)))
      (release-ticket-cells! rt ticket)
      (dissoc! (a (runtime-field rt :finalization) 0) (a ticket x-id))
      (put run r-exit nil) (put run r-status :running)
      (boundary! rt (when (runtime-field rt :audit)
                      {:t :finalization-resume :w (runtime-field rt :world)
                       :n (a ticket x-id) :th :engine}))
      true)))

(defn await-finalization-effect!
  "Protected one-shot callback wait for the opt-in native CPS exit profile.
  Retirement preserves this wait; its producer is never cancelled by retirement."
  ([start resolve reject]
   (await-finalization-effect! start resolve reject resolve reject))
  ([start resolve reject resume-resolve resume-reject]
   (let [frame (current-activation) rt (a frame 0) run (a frame 1)
         ticket (locked rt
                        (when-not (runtime-field rt :finalization)
                          (throw (ex-info "Protected CPS exit profile is disabled" {:error :profile-disabled})))
                        (let [cleanup (or (a frame 8)
                                          (when (and run (= :unwinding (a run r-status)))
                                            (cleanup-adopt! rt run)))
                              ticket (or cleanup
                                         (do (check-running! run)
                                             (when-not (and run (identical? run (current (a run r-node)))
                                                            (nil? (a run r-exit)))
                                               (throw (ex-info "Finalization wait requires the current physical slice" {})))
                                             (doto (slots 18)
                                               (put x-id (exit-id rt run)) (put x-anchor (run-anchor rt run))
                                               (put x-kind :cps-finalization) (put x-cells (id-dict))
                                               (put x-run run))))
                              sequence (inc (long (or (a ticket x-seq) (when run (a run r-finalization-seq)) 0)))]
                          (when (and cleanup (not= :claimed (a ticket x-phase)))
                            (throw (ex-info "Cleanup wait requires a claimed ticket" {})))
                          (put ticket x-phase :waiting) (put ticket x-seq sequence)
                          (put ticket x-address (if run (a run r-address) (a ticket x-address)))
                          (put ticket x-resolve resume-resolve) (put ticket x-reject resume-reject)
                          (put ticket x-value nil) (put ticket x-delivered false) (put ticket x-physical true)
                          (when-not cleanup
                            (put run r-status :parked) (put run r-finalization-seq sequence) (put run r-exit ticket))
                          (assoc! (a (runtime-field rt :finalization) 0) (a ticket x-id) ticket)
                          (boundary! rt (when (runtime-field rt :audit)
                                          (if cleanup {:t :cleanup-park :th :engine}
                                              {:t :finalization-wait :w (runtime-field rt :world) :th :engine})))
                          ticket))
         id (a ticket x-id) sequence (a ticket x-seq)]
     (try (start (protected-callback rt id sequence false) (protected-callback rt id sequence true))
          (catch #?(:clj Throwable :cljs :default) error
            ((protected-callback rt id sequence true) error)))
    ;; Synchronous settlement consumes readiness on this exact frame. External
    ;; delivery only records readiness until the suspending slice returns.
     (let [resume? (locked rt
                           (when (= :ready (a ticket x-phase))
                             (if (= :cps-finalization (a ticket x-kind))
                               (resume-finalization! rt ticket)
                               (when-not (a frame 8) (cleanup-adopt! rt run) true))))]
       (when resume?
         (deliver-value! resolve reject (a ticket x-value) (a ticket x-failed)))))))

(defn- finish-cleanup-slice! [rt ticket]
  (put ticket x-physical false)
  (when (= :returning (a ticket x-phase)) (release-cleanup! rt ticket))
  (when (#{:claimed} (a ticket x-phase))
    (throw (ex-info "Cleanup returned without a completion or protected wait" {})))
  (queue-cleanup! rt ticket))

(defn- claim-cleanup! [rt ticket]
  (locked rt
          (put ticket x-queued false)
          (when (and (identical? ticket (find! (a (runtime-field rt :finalization) 0) (a ticket x-id)))
                     (= :ready (a ticket x-phase)) (not (a ticket x-physical)))
            (let [live? (= :cps-finalization (a ticket x-kind)) run (when live? (a ticket x-run))
                  frame (a (runtime-field rt :counters) 5)]
              (when (or (not live?) (and run (identical? run (current (a run r-node))) (= :parked (a run r-status))))
                (put ticket x-physical true)
                (when run (put run r-physical true))
                (put (runtime-field rt :thread) 0 run) (put (runtime-field rt :thread) 1 true)
                (put (runtime-field rt :thread) 2 (runtime-field rt :world))
                (when run (put run r-address (a ticket x-address)))
                (put frame 0 rt) (put frame 1 run) (put frame 2 -1)
                (when-not live?
                  (end-deferred-protection! rt ticket)
                  (put frame 8 ticket) (put (runtime-field rt :thread) 4 ticket) (put ticket x-phase :claimed))
                (if live? (resume-finalization! rt ticket)
                    (boundary! rt (when (runtime-field rt :audit) {:t :cleanup-claim :n (a ticket x-id) :th :engine})))
                frame)))))

(defn- invoke-cleanup! [rt ticket]
  (when-let [frame (claim-cleanup! rt ticket)]
    (let [run (a frame 1)
          callback (if (a ticket x-delivered)
                     (a ticket (if (a ticket x-failed) x-reject x-resolve))
                     (a ticket x-reject))
          value (if (a ticket x-delivered) (a ticket x-value) (a ticket 14))]
      (try
        (public-slice! rt run ticket nil
                       (fn [] (with-activation frame
                                (try
                                  (cps/invoke-continuation callback value)
                                  (catch #?(:clj Throwable :cljs :default) error
                                    (complete! rt run error true))))))
        (finally
          (finish-slice! rt run frame)
          (dotimes [i 14] (put frame i nil)))))))

(defn- complete! [requested run value failed?]
  (let [rt (execution-runtime requested)]
    (locked rt
            (let [frame (current-activation)
                  cleanup (or (when frame (a frame 8))
                              (when (and run (= :unwinding (a run r-status))) (cleanup-adopt! rt run)))]
              (if cleanup (cleanup-return! rt cleanup value failed?)
                  (let [node (a run r-node)]
                    (when (and (identical? run (current node)) (= :running (a run r-status)))
                      (when-not (a node n-complete)
                        (mark-graph! rt node) (mark-graph! rt (owner-node (a node n-owner))))
                 ;; Completion and outcome share one slot: false/true/:error.
                 ;; Cache checks need truthiness; delivery reads the error tag.
                      (put node n-complete (if failed? :error true))
                      (put node n-dirty (boolean (a run r-validation-lost))) (put node n-value value)
                      (put run r-status :completed) (put run r-cancel-cont nil)
                      (push! (runtime-field rt :events)
                             (doto (slots 4) (put 0 node) (put 1 value) (put 3 failed?)
                                   (put 2 (put (runtime-field rt :counters) 2
                                               (inc (max (long (a (runtime-field rt :counters) 1))
                                                         (long (a (runtime-field rt :counters) 2))))))))
                      (each-copy! [previous (values (a node n-runs))]
                                  (when (and (not (identical? previous run)) (basis-status? (a previous r-status)))
                                    (retire! rt previous)))
                      (mark! rt node))
                    (boundary! rt (when (runtime-field rt :audit)
                                    {:t :t07 :w (runtime-field rt :world) :r [(a node n-id) (a run r-gen)]
                                     :value (diagnostic-value value failed?)}))))))))

(defn- reenter!
  ([rt node trigger] (reenter! rt node trigger :reactive))
  ([rt node trigger cause]
   (let [previous (current node) work? (work-status? (a previous r-status))
         order (if trigger (a trigger o-order) -1)]
     (each-copy! [old (values (a node n-runs))]
                 (when (= :stale (a old r-status)) (retire! rt old)))
     (let [run (start! rt node (a previous r-owner) true)]
       (when (and (not= :dirty cause) (or (a previous r-validation-lost) (a node n-dirty)))
         (put run r-validation-lost true))
       (when work? (put previous r-status :stale))
      ;; A completed predecessor still supplies the continuation's prefix.
      ;; Earlier consumed awaits retain captured values too. The triggering
      ;; await stays behind so its successor rechecks the debtor's fresh state.
       (each-copy! [ob (a previous r-obs)]
                   (if (or (and (= :track (a ob o-kind)) (<= (long (a ob o-order)) (long order)))
                           (and (= :await-reactive (a ob o-kind)) (a ob o-standing)
                                (= :consumed (a ob o-slot)) (< (long (a ob o-order)) (long order))))
                     (do (remove! (a previous r-obs) ob) (put ob o-run run) (reactive-delta! previous -1) (reactive-delta! run 1)
                         (put ob o-creditor-generation (a run r-gen))
                         (put ob o-creditor-node node) (add-run! run r-obs ob)
                         (when (= :await-reactive (a ob o-kind))
                           (adopt! rt (a ob o-debtor) run)))
                     (when work? (end-ob! rt ob))))
       (custody-adopt! rt previous run order)
       (each-copy! [scope (or (scope-children rt previous) empty-members)]
                   (when (< (long (a (owner-storage scope) s-order)) (long order))
                     (scope-parent! rt scope run)
                     (doseq [owned (scope-owned-nodes rt run)] (mark-graph! rt owned))
                     (mark-graph! rt node)))
       (each-copy! [child (a previous r-created)]
                   (when (< (long (a child n-order)) (long order))
                     (owner! rt child run)
                     (when (a child n-creator) (creator! rt child run))
                     (uncreate! previous child) (creation! run child)
                     (each! [cr (values (a child n-runs))]
                            (when (identical? previous (a cr r-owner))
                              (remove! (a previous r-childruns) cr) (put cr r-owner run) (add-run! run r-childruns cr)))))
       (schedule! rt node trigger)))))

(defn- subscriber-buffer! [rt node]
  (let [n (count! (a node n-dependents))
        old (a (runtime-field rt :counters) 4)
        buffer (if (< (alength ^objects old) n)
                 (put (runtime-field rt :counters) 4 (slots (max n (* 2 (alength ^objects old))))) old)]
    #?(:clj (.toArray ^java.util.Collection (a node n-dependents) ^objects buffer)
       :cljs (.copyInto (a node n-dependents) buffer))
    n))

(defn- process-event! [rt event]
  (let [node (a event 0) value (a event 1) failed? (a event 3)
        n (subscriber-buffer! rt node)
        dependents (a (runtime-field rt :counters) 4)
        order (when (runtime-field rt :audit) (mapv #(vector :o (a (a dependents %) o-id)) (range n)))]
    (when (identical? event (a node n-source-event)) (put node n-source-event nil))
    (when (#{:atom :deferred :mailbox} (a node n-kind))
      (note-cell-gc-blocker-change! rt (a node n-id)))
    (try
      (dotimes [index n]
        (let [ob (a dependents index)]
          (if-let [run (a ob o-run)]
            (if (= :consumed (a ob o-slot))
              (reenter! rt (a ob o-creditor-node) ob)
              (when (and (a ob o-live) (= :parked (a run r-status)))
                (put ob o-slot :consumed) (put ob o-value value) (put ob o-delivery-error failed?)
                (when-not (a ob o-standing) (end-ob! rt ob))
                (put run r-status :running)
                (schedule! rt (a ob o-creditor-node) ob)))
            (do (push! (runtime-field rt :hosts)
                       (doto (slots 2) (put 0 (a ob (if failed? o-failure o-success))) (put 1 value)))
                (when (or (= :deref (a ob o-kind))
                          (and (a node n-complete) (not (reactive? (current node)))))
                  (end-ob! rt ob))))))
      (boundary! rt (when (runtime-field rt :audit) {:t :t08 :w (runtime-field rt :world) :e (a node n-id) :value (diagnostic-value value failed?)
                                                     :delivery-order order}))
      (finally (dotimes [i n] (put dependents i nil))))))

(defn- poll-ready! [^ArenaState dispatch]
  #?(:clj (.poll ^java.util.PriorityQueue (.-ready dispatch))
     :cljs (let [heap (.-ready dispatch) n (.-length heap)]
             (when (pos? n)
               (let [head (aget heap 0) tail (.pop heap) n (dec n)]
                 (when (pos? n)
                   (loop [index 0]
                     (let [left (inc (* 2 index))]
                       (if (< left n)
                         (let [right (inc left)
                               child (if (and (< right n) (< (a (aget heap right) n-rank)
                                                             (a (aget heap left) n-rank))) right left)
                               below (aget heap child)]
                           (if (< (a below n-rank) (a tail n-rank))
                             (do (aset heap index below) (recur child))
                             (aset heap index tail)))
                         (aset heap index tail)))))
                 head)))))

(declare drain!)
(defn- finish-slice! [rt run frame]
  (locked rt
          (let [ticket (or (when frame (a frame 8)) (when run (a run r-exit)))
                retired-run (or run (when ticket
                                      (first (filter #(= (run-id %) (nth (a ticket x-id) 2))
                                                     (items (a (runtime-field rt :counters) 6))))))]
            (when-let [consumer (when frame (when (> (alength ^objects frame) 13) (a frame 13)))]
              (mailbox-return! rt consumer))
            (when run (put run r-physical false))
            (when ticket (finish-cleanup-slice! rt ticket))
            (put (runtime-field rt :thread) 0 nil) (put (runtime-field rt :thread) 4 nil)
            (when (and retired-run (= :unwinding (a retired-run r-status))
                       (zero? (long (or (a retired-run r-timers) 0)))
                       (or (nil? ticket) (nil? (find! (a (runtime-field rt :finalization) 0) (a ticket x-id)))))
              (forget-run! rt retired-run))
            (boundary! rt (when (runtime-field rt :audit) {:t :t38 :th :engine})))))

(defn- claim-slice! [rt node]
  (locked rt
          (let [run (current node) ob (a node n-resume)]
            (put node n-ready false) (put node n-resume nil)
            (when (and run (= :running (a run r-status)) (= (a run r-gen) (a node n-pending-generation)))
              (when ob (rank! run (a ob o-debtor)))
              (put run r-physical true)
              (when (runtime-field rt :finalization) (put run r-entered true))
              (put (runtime-field rt :thread) 0 run) (put (runtime-field rt :thread) 1 true) (put (runtime-field rt :thread) 2 (runtime-field rt :world))
              (if-let [consumer (when (and ob (not (a ob o-delivery-error))) (a ob o-mailbox))]
                (mailbox-enter! rt consumer [:mailbox-frame (a consumer b-id)] false true)
                (boundary! rt (when (runtime-field rt :audit) {:t :slice-enter :w (runtime-field rt :world) :r [(a node n-id) (a run r-gen)] :th :engine})))
              (let [frame (a (runtime-field rt :counters) 5) debtor (when ob (a ob o-debtor))]
                (put run r-address (when ob (a ob o-address)))
                (put frame 0 rt) (put frame 1 run) (put frame 2 (if ob (a ob o-order) -1))
                (put frame 3 ob) (put frame 4 (a node n-body))
                (put frame 13 (when (and ob (not (a ob o-delivery-error))) (a ob o-mailbox)))
                (put frame 5 (when debtor (a debtor n-value)))
                (put frame 6 (when ob (a ob o-body)))
                (put frame 7 (when ob (a ob o-last)))
                (when (and ob (= :track (a ob o-kind)) (identical? run (a ob o-run))
                           (= (a run r-gen) (a ob o-creditor-generation)))
                  (put ob o-last (a frame 5))
                  (put frame 9 (when debtor (public-track-interval! debtor ob false))))
                frame)))))

(defn- invoke-slice! [rt activation]
  (let [run (a activation 1) ob (a activation 3)]
    (if ob
      (let [moved? (and (identical? run (a ob o-run)) (= (a run r-gen) (a ob o-creditor-generation)))]
        (if (= :track (a ob o-kind))
          (if moved?
            (cps/invoke-continuation (a ob o-resolve) (or (a activation 9) (iv/->Interval (a activation 7) (a activation 5) nil)))
            (let [order (a ob o-order)
                  value (register-track! rt run order (a (a ob o-debtor) n-id) (a ob o-resolve) (a ob o-reject))]
              (put activation 2 order)
              (cps/invoke-continuation (a ob o-resolve) (or (a activation 9) (iv/->Interval (a activation 7) value nil)))))
          (if moved?
            (deliver-cont! ob (a ob o-value))
            (do (put activation 2 (dec (long (a ob o-order))))
                (await-id-effect! (a (a ob o-debtor) n-id) nil (a activation 6)
                                  (a ob o-resolve) (a ob o-reject) (a ob o-resolve) (a ob o-reject))))))
      ((a activation 4)
       (fn [value] (complete! rt (a (current-activation) 1) value false))
       (fn [error] (complete! rt (a (current-activation) 1) error true))))))

(defn- execute! [rt node]
  (when-let [activation (claim-slice! rt node)]
    (let [run (a activation 1) ob (a activation 3)]
      (try
        (public-slice! rt run nil (when-not ob (a activation 4))
                       (fn [] (with-activation activation
                                (try (invoke-slice! rt activation)
                                     (catch #?(:clj Throwable :cljs :default) error
                                       (try
                                         (if ob (cps/invoke-continuation (a ob o-reject) error)
                                             (complete! rt run error true))
                                         (catch #?(:clj Throwable :cljs :default) rejected
                                           (complete! rt run rejected true))))))))
        (finally
          (finish-slice! rt run activation)
          (dotimes [i 14] (put activation i nil)))))))

(defn- next-custody-cleanup! [^ArenaState dispatch]
  (when-let [service (let [state (a (.-counters dispatch) 11)] (when-not (map? state) state))]
    (some (fn [world]
            (when-not (custody-data-world? world)
              (when-let [profile (runtime-field world :finalization)]
                (when-let [ticket (pop! (a profile 2))]
                  (doto (slots 3) (put 0 :cleanup) (put 1 ticket) (put 2 world))))))
          (values (:worlds @service)))))

(defn- next-dispatch! [rt ^ArenaState dispatch]
  (locked rt
          (if-let [post (pop! (.-posts dispatch))]
            post
            (if-let [event (pop! (.-events dispatch))]
              (do (cond (custody-event? event) (custody-dispatch! (a event 1) event)
                        (= 9 (alength ^objects event)) (process-mailbox-post! (a event 0) event)
                        (= 7 (alength ^objects event)) (assign-deferred! (a event 0) event)
                        :else (process-event! (a (a event 0) n-runtime) event))
                  :event)
              (or (when-let [profile (.-finalization dispatch)]
                    (when-let [ticket (pop! (a profile 2))]
                      (doto (slots 3) (put 0 :cleanup) (put 1 ticket) (put 2 rt))))
                  (next-custody-cleanup! dispatch)
                  (poll-ready! dispatch) (pop! (.-hosts dispatch)))))))

(defn drain!
  ([rt] (drain! rt @(runtime-field rt :arena-cell)))
  ([rt ^ArenaState dispatch]
   (let [draining (.-draining dispatch)]
     (when (compare-and-set! draining false true)
       (binding [cps/*in-trampoline* false]
         (let [failure
               (try
                 (loop [failure nil]
                   (if-let [entry (next-dispatch! rt dispatch)]
                     (if (and (not= :event entry) (= 1 (alength ^objects entry)))
                    ;; Logical cancellation is already committed. A failed
                    ;; detach must not strand other cancellation/delivery work.
                       (let [error (try ((a entry 0)) nil
                                        (catch #?(:clj Throwable :cljs :default) error [error]))]
                         (recur (or failure error)))
                       (if (and (not= :event entry) (= 2 (alength ^objects entry)))
                      ;; Host observers own their exceptions. Finish committed
                      ;; deliveries, including reentrant registrations, before
                      ;; reporting the first error to the drain's caller.
                         (let [callback (a entry 0) value (a entry 1)
                               error (try
                                       (callback value)
                                       nil
                                       (catch #?(:clj Throwable :cljs :default) error [error]))]
                           (recur (or failure error)))
                         (do
                           (when-not (= :event entry)
                             (if (= 3 (alength ^objects entry))
                               (invoke-cleanup! (a entry 2) (a entry 1))
                               (execute! (a entry n-runtime) entry)))
                           (recur failure))))
                     failure))
                 (finally (reset! draining false)))]
           (let [later-failure
                 (try
                   (when (locked rt (or (queued? (runtime-field rt :posts)) (queued? (runtime-field rt :events)) (queued? (runtime-field rt :hosts))
                                        (when-let [profile (runtime-field rt :finalization)] (queued? (a profile 2)))
                                        #?(:clj (not (.isEmpty ^java.util.PriorityQueue (runtime-field rt :ready)))
                                           :cljs (pos? (.-length (runtime-field rt :ready))))))
                     (drain! rt))
                   nil
                   (catch #?(:clj Throwable :cljs :default) error [error]))]
          ;; A tagged error also preserves JavaScript's `throw null/false`.
             (when-let [error (or failure later-failure)] (throw (first error))))))))))

(defn- observe-token! [rt id token body success failure]
  (let [ob (locked rt
                   (when (and (current-activation) (identical? rt (a (current-activation) 0)))
                     (check-running! (a (current-activation) 1)))
                   (check-token! rt token)
                   (when (and (nil? (find! (runtime-field rt :nodes) id)) (parent-node rt id))
                     (throw (ex-info "Foreign invocation is outside this slice" {:id id})))
                   (let [owner (selected-owner rt)
                         node (or (find! (runtime-field rt :nodes) id) (node! rt id :spin owner))
                         cached? (and (a node n-complete) (not (a node n-dirty)) (not (work-status? (some-> (current node) (a r-status)))))]
                     (put node n-body body)
                     (when-not (a node n-owner) (owner! rt node owner))
                     (touch! rt node token)
                     (when-not (or cached? (work-status? (some-> (current node) (a r-status)))) (start! rt node owner false))
                     (let [ob (ob! rt :callback node nil 0 nil nil)]
                       (put ob o-success success) (put ob o-failure failure)
                       (when cached?
                         (push! (runtime-field rt :hosts) (doto (slots 2) (put 0 (a ob (if (= :error (a node n-complete)) o-failure o-success)))
                                                                (put 1 (a node n-value))))
                         (when-not (reactive? (current node)) (end-ob! rt ob)))
                       (boundary! rt (when (runtime-field rt :audit) (cond-> {:t :t04 :w (runtime-field rt :world) :e id :tok (a token t-id) :mode :callback}
                                                                       (not (root-owner? owner)) (assoc :scope (owner-id owner)))))
                       ob)))]
    (drain! rt)
    (fn []
      (admit-native-effect!)
      (locked rt
              (check-native-caller! rt)
              (end-ob! rt ob)
              (boundary! rt (when (runtime-field rt :audit) {:t :unsubscribe :w (runtime-field rt :world) :o [:o (a ob o-id)]})))
      (drain! rt))))

(defn observe! [requested handle success failure]
  (try
    (observe-token! (execution-runtime requested) (:id handle) (:token handle) (:body handle) success failure)
    (finally #?(:clj (java.lang.ref.Reference/reachabilityFence handle) :cljs nil))))

(defn invoke-computation!
  "Typed public invocation; token identity is local to the runtime family."
  ([requested target id body success failure]
   (try
     (admit-world-switch! requested)
     (let [rt (canonical-runtime requested)]
       (locked rt
               (when (and (nil? (find! (runtime-field rt :nodes) id)) (parent-node rt id))
                 (throw (ex-info "Foreign invocation is outside this slice" {:id id}))))
       (observe-token! rt id (portable-token! rt target id false) body success failure))
     (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))
  ([requested target id body success failure mode]
   (invoke-public-computation! requested target id body success failure mode)))

(defn- source-node! [rt source unwinding?]
  (let [node (find! (runtime-field rt :nodes) (:id source))]
    (when (and (:allocation source)
               (not (identical? (:allocation source) (find! (a (runtime-field rt :finalization) 3) (:id source)))))
      (throw (ex-info "Released source allocation" {:id (:id source)})))
    (when-not (or (and unwinding? (nil? node))
                  (and node (= :signal (a node n-kind)) (or (a node n-owner) unwinding?)))
      (throw (ex-info "Released source" {:id (:id source)})))
    node))

(def ^:private engine-state-keys
  #{:nodes :spin-tracking :subscriptions :track-subscriptions :await-conts
    :entities :runs :obligations :queue :lineage :root :status :admission :seal-seq
    :seq :serial :clock :handles :threads :gc :principals :global :cleanup-targets :scopes :next-scope :scope-balance :pins
    :fdeps :releasing :cuts :caps :registry :native :cleanup-cells :atoms :listeners :source-gc :addressing})

(defn- engine-path? [path]
  (let [key (first path)]
    (or (contains? engine-state-keys key)
        (and (keyword? key) (#{"engine" "lifetime"} (namespace key))))))

(defn- application-write! [path]
  (when (or (empty? path) (engine-path? path))
    (throw (ex-info "Engine state requires a typed operation" {:error :engine-state-read-only :path path}))))

(defn- application-roots [rt]
  ;; The family gate is held by the caller. Keep immutable roots, never a
  ;; mutable row alias, and do not retain these borrowed views after the call.
  (loop [world rt result []]
    (if world
      (recur (runtime-field world :parent)
             (conj result [world @(runtime-field world :extension-state)]))
      result)))

(defn- application-values [roots]
  (reduce (fn [parent [_ {:keys [values shadowed]}]]
            (reduce (fn [result path]
                      (if (= 1 (count path))
                        (assoc-in result path (get-in values path))
                        (let [[group cell] path parent (get result group)]
                          (assoc result group (assoc (if (map? parent) parent {}) cell (get-in values path))))))
                    parent shadowed))
          {} (reverse roots)))

(defn- application-group-base [roots group]
  ;; Only the shape is needed for a map group; return a vector/scalar base
  ;; directly so nested vector edits can preserve the complete vector value.
  (some (fn [[_ {:keys [values shadowed map-groups]}]]
          (cond (contains? shadowed [group]) [true (get values group)]
                (contains? map-groups group) [true {}])) roots))

(defn- application-value [roots path]
  (if (< (count path) 2)
    (get-in (application-values roots) path)
    (let [top (first path) group [top] cell (subvec path 0 2)]
      (loop [roots (seq roots)]
        (when-let [[_ {:keys [values shadowed map-groups]}] (first roots)]
          (cond
            (or (contains? shadowed group) (contains? shadowed cell)) (get-in values path)
            (and (contains? map-groups top)
                 (not (map? (second (application-group-base (next roots) top))))) nil
            :else (recur (next roots))))))))

(defn- application-candidate [roots path value]
  (let [state (second (first roots))
        group [(first path)] cell (if (= 1 (count path)) group (subvec path 0 2))
        base (second (application-group-base roots (first path)))]
    (if (and (> (count path) 1) (some? base) (not (map? base)))
      (application-candidate roots group (assoc-in base (subvec path 1) value))
      (let [values (if (or (= 1 (count path)) (contains? (:shadowed state) group)
                           (contains? (:shadowed state) cell))
                     (:values state)
                     (assoc-in (:values state) cell (application-value roots cell)))
            shadowed (:shadowed state)
            shadowed (if (= 1 (count path))
                       (set (remove #(= (first %) (first path)) shadowed)) shadowed)
            updated-values (assoc-in values path value)
            updated-shadowed (if (contains? shadowed group) shadowed (conj shadowed cell))
            map-groups (if (= 1 (count path)) (disj (:map-groups state) (first path))
                           (if (contains? shadowed group) (:map-groups state)
                               (conj (:map-groups state) (first path))))]
        (if (and (identical? updated-values (:values state)) (= updated-shadowed (:shadowed state))
                 (= map-groups (:map-groups state)))
          state
          {:values updated-values :shadowed updated-shadowed :map-groups map-groups})))))

(defn- application-roots-current? [roots]
  (every? (fn [[world before]] (identical? before @(runtime-field world :extension-state))) roots))

(defn read-application-state
  "PState application cells and explicit immutable engine diagnostics. Reads
   of a cell borrow no mutable engine row. Engine paths cannot be mutated."
  [requested path]
  (when-not (and (seq path) (engine-path? path)) (admit-native-effect!))
  (let [rt requested]
    (cond
      (empty? path) (let [[graph roots] (locked rt (check-native-caller! rt) [(snapshot rt) (application-roots rt)])]
                      (merge graph (application-values roots)))
      (#{:atoms :listeners} (first path))
      (locked rt
              (get-in (case (first path)
                        :atoms (into {} (for [node (values (runtime-field rt :nodes))
                                              :when (= :atom (a node n-kind))]
                                          [(a node n-id) (a node n-value)]))
                        :listeners (into {} (for [[id aux] (map-value (a (runtime-field rt :managed-cells) 0))
                                                  :when (seq (a aux 1))]
                                              [id (a aux 1)])))
                      (subvec path 1)))
      (engine-path? path) (get-in (snapshot rt) path)
      :else (application-value (locked rt (check-native-caller! rt) (application-roots rt)) path))))

(defn- check-application-caller! [rt]
  (world-open! rt)
  ;; Called under the target gate. Related worlds share that gate; unrelated
  ;; worlds use the explicit admission check before acquiring the target.
  (when-let [frame (current-activation)]
    (when (identical? (runtime-field rt :gate) (runtime-field (a frame 0) :gate))
      (check-running! (a frame 1)))))

(defn swap-application-state!
  "User transformations run outside the family gate. Commit retries if any
   application cell changed, and is serialized with fork/capture boundaries."
  [requested path f args]
  (application-write! path)
  (let [rt requested state (runtime-field rt :extension-state)]
    (admit-world-switch! rt)
    (loop []
      (let [roots (locked rt (check-application-caller! rt) (application-roots rt)) before (second (first roots))
            value (application-value roots path)
            after (if (seq args) (apply f value args) (f value))
            candidate (application-candidate roots path after)
            _ (admit-world-switch! rt)
            committed? (locked rt
                               (check-application-caller! rt)
                               (when (application-roots-current? roots)
                                 (compare-and-set! state before candidate)))]
        (if committed? after (recur))))))

(defn cas-application-state! [requested path old-value new-value]
  (application-write! path)
  (let [rt requested state (runtime-field rt :extension-state)]
    (admit-world-switch! rt)
    (loop []
      (let [roots (locked rt (check-application-caller! rt) (application-roots rt)) before (second (first roots))]
        ;; Equality and key hashing may call user code, including a reentrant
        ;; update. Construct the candidate outside the gate, then compare the
        ;; complete immutable root by identity so those updates are preserved.
        (if (= old-value (application-value roots path))
          (let [candidate (application-candidate roots path new-value)
                _ (admit-world-switch! rt)]
            (if (locked rt (check-application-caller! rt)
                        (when (application-roots-current? roots)
                          (compare-and-set! state before candidate)))
              true (recur)))
          false)))))

(defn read-signal [requested source]
  (let [rt (execution-runtime requested)]
    (check-source! rt source)
    (locked rt
            (if-let [[key cell] (cleanup-cell! rt source)]
              (do (boundary! rt (when (runtime-field rt :audit) {:t :cleanup-cell :th :engine :cell key})) (a cell 1))
              (a (source-node! rt source false) n-value)))))

(defn- enqueue-source! [rt node value]
  (let [old (a node n-source-event)
        event (or old (slots 4))]
    ;; Source events invalidate cached observations; they are not a lossless log.
    (when old
      #?(:clj (.remove ^java.util.ArrayDeque (runtime-field rt :events) old)
         :cljs (.remove (runtime-field rt :events) old)))
    (put node n-source-event event)
    (put event 0 node) (put event 1 value)
    (put event 2 (put (runtime-field rt :counters) 2
                      (inc (max (long (a (runtime-field rt :counters) 1))
                                (long (a (runtime-field rt :counters) 2))))))
    (push! (runtime-field rt :events) event)))

(defn- write-source!
  ([rt node source value] (write-source! rt node source value true))
  ([rt node source value publish?]
   (when node
     (put node n-value value)
     (when publish? (enqueue-source! rt node value)))
   (boundary! rt (when (runtime-field rt :audit)
                   (cond-> {:t :signal-write :w (runtime-field rt :world) :e (:id source) :value value}
                     (not publish?) (assoc :publish? false)
                     (when-let [frame (current-activation)]
                       (identical? (runtime-field rt :owner-root)
                                   (runtime-field (a frame 0) :owner-root)))
                     (assoc :th :engine))))))

(defn set-signal! [requested source value]
  (let [rt (execution-runtime requested)
        _ (check-source! rt source)
        unwinding? (when-let [run (when (current-activation) (a (current-activation) 1))]
                     (= :unwinding (a run r-status)))]
    (locked rt
            (if-let [[key cell] (cleanup-cell! rt source)]
              (do (put cell 1 value)
                  (boundary! rt (when (runtime-field rt :audit) {:t :cleanup-cell :th :engine :cell key :value value})))
              (write-source! rt (source-node! rt source unwinding?) source value)))
    (drain! rt)))

;; Managed atom payloads are immutable. Aux slots are [allocation watches claims];
;; world slots are [aux-by-id pending-receipts receipt-seen?]. Neither
;; contains a wrapper/anchor, and host cleanup retains the family home weakly.
(defn- same-cell-world? [left right]
  (identical? (runtime-field left :owner-root) (runtime-field right :owner-root)))

(defn- canonical-runtime [requested]
  ;; Lexical scope restoration decorates a context record. Engine objects and
  ;; queues must always name the canonical world registered in the family;
  ;; the requested record is retained separately only for listener bindings.
  (locked requested
          (let [rt (find! (runtime-field requested :family) (runtime-field requested :world))]
            (when-not (and rt (not (custody-data-world? rt)) (same-cell-world? requested rt))
              (throw (ex-info "Unknown execution world" {:error :unknown-world})))
            rt)))

(defn- check-address-slice! [frame]
  (when frame
    (let [run (a frame 1) node (when run (a run r-node))]
      (when (or (a frame 8) (= :unwinding (when run (a run r-status))))
        (throw (ex-info "Cleanup cannot construct ordinary computations" {:error :cleanup-only})))
      (when-not (and node (identical? run (current node)) (= :running (a run r-status)))
        (throw (ex-info "Addressing requires the current ordinary slice" {:error :stale-addressing-slice}))))))

(defn next-trace-address!
  "Advance an owned root/run cursor, hashing outside the engine gate."
  [requested prefix source-loc]
  (let [rt (canonical-runtime requested)
        frame (current-activation)
        caller (when frame (a frame 0))
        local? (and caller (same-cell-world? rt caller))]
    ;; A foreign explicit target has root authority, after admission at the
    ;; initiating slice's own gate. No foreign run is read under this gate.
    (when (and frame (not local?))
      (locked caller (check-address-slice! frame)))
    (loop []
      (let [[receipt run seed]
            (locked rt
                    (when local? (check-address-slice! frame))
                    (let [run (when local? (a frame 1))
                          receipt (if run (a run r-address) (a (runtime-field rt :trace-address) 0))]
                      [receipt run (when run (a (a run r-node) n-id))]))
            previous (if receipt (first receipt)
                         (when run (addressing/body-start-chain-head seed)))
            id (keyword (str prefix "-" (addressing/chain-hash source-loc previous)))
            committed?
            (locked rt
                    (when local? (check-address-slice! frame))
                    (let [current (if run (a run r-address) (a (runtime-field rt :trace-address) 0))]
                      (when (identical? receipt current)
                        ;; A fresh immutable receipt is the revision witness,
                        ;; even if two hashes happen to produce equal heads.
                        (if run (put run r-address [id])
                            (put (runtime-field rt :trace-address) 0 [id]))
                        true)))]
        (if committed? id (recur))))))

(defn- cell-backing [rt id]
  (loop [world rt]
    (when world
      (if-let [node (find! (runtime-field world :nodes) id)]
        [world node (find! (a (runtime-field world :managed-cells) 0) id)]
        (when (= :following (:mode (runtime-field world :lineage)))
          (recur (runtime-field world :parent)))))))

(defn- ordinary-cell-node [rt id]
  ;; Called only under the family gate. Reads consume the immutable payload
  ;; before releasing that gate, so no backing vector or mutation view escapes.
  (loop [world rt]
    (when world
      (if-let [node (find! (runtime-field world :nodes) id)]
        (let [aux (find! (a (runtime-field world :managed-cells) 0) id)]
          (when (and aux (= :atom (a node n-kind)) (a node n-owner)
                     (= id (a aux 0)))
            node))
        (when (= :following (:mode (runtime-field world :lineage)))
          (recur (runtime-field world :parent)))))))

(defn- cleanup-cell-access? [rt]
  (when-let [frame (current-activation)]
    (and (same-cell-world? rt (a frame 0))
         (or (active-mailbox-callback)
             (when-let [operation (active-operation)] (operation-retired? operation))
             (a frame 8)
             (= :unwinding (some-> (a frame 1) (a r-status)))))))

(defn- check-cell-caller! [rt]
  (when-not (cleanup-cell-access? rt) (world-open! rt))
  (if-let [receipt (active-mailbox-callback)]
    (mailbox-callback-check! rt receipt)
    (if-let [operation (active-operation)]
      (operation-check! rt operation)
      (when-let [frame (current-activation)]
        (when (identical? (runtime-field rt :gate) (runtime-field (a frame 0) :gate))
          (check-running! (a frame 1)))))))

(defn- cell-view! [rt id]
  (let [frame (current-activation)
        active (when (and frame (same-cell-world? rt (a frame 0))) (a frame 0))]
    (if-let [[key retained] (when active (cleanup-cell! active {:id id :allocation id}))]
      (do (when-not (= :atom (a retained 0))
            (throw (ex-info "Not a retained atom" {:error :missing-cell :id id})))
          {:cleanup key :retained retained :payload (a retained 1)})
      (do
        (check-cell-caller! rt)
        (let [[backing node aux] (cell-backing rt id)
              watch-aux (find! (a (runtime-field rt :managed-cells) 0) id)]
          (when-not (and node aux (= :atom (a node n-kind)) (a node n-owner)
                         (= id (a aux 0)))
            (throw (ex-info "Released managed atom" {:error :missing-cell :id id})))
          {:backing backing :node node :aux aux :owner (a node n-owner)
           :owner-stamp (owner-id (a node n-owner))
           :payload (a node n-value) :watch-aux watch-aux
           :watches (if watch-aux (a watch-aux 1) {})})))))

(defn- same-cell-view? [before after]
  (and (identical? (:retained before) (:retained after))
       (identical? (:node before) (:node after))
       (identical? (:aux before) (:aux after))
       (identical? (:owner before) (:owner after))
       (= (:owner-stamp before) (:owner-stamp after))
       (identical? (:payload before) (:payload after))))

(defn- retain-cell-operation! [rt id]
  (locked rt
          (let [view (cell-view! rt id)]
            (when-let [aux (:aux view)] (put aux 2 (inc (long (a aux 2)))))
            (assoc view :claims (volatile! (if-let [aux (:aux view)] [aux] []))))))

(defn- release-cell-operation! [rt view]
  (locked rt
          (doseq [aux @(:claims view)]
            (put aux 2 (dec (long (a aux 2))))
            (note-cell-gc-blocker-change! rt (a aux 0)))
          (vreset! (:claims view) [])
          (retry-cell-gc! rt)))

(defn- localize-cell! [rt id view claims]
  (if (same-cell-world? rt (:backing view)) view
      (let [payload (:payload view) node (node! rt id :atom (runtime-field rt :owner-root))
            aux (or (:watch-aux view)
                    (doto (slots 3) (put 0 id) (put 1 {}) (put 2 0)))
            collected (find! (a (runtime-field (:backing view) :managed-cells) 1) id)]
        (put node n-value payload)
        (assoc! (a (runtime-field rt :managed-cells) 0) id aux)
        (note-cell-gc-blocker-change! rt id)
        ;; A raw-ID operation can outlive the final wrapper and its Cleaner
        ;; notification. Protect its new local storage through publication,
        ;; listener dispatch and drain, in addition to its original backing.
        (put aux 2 (inc (long (a aux 2))))
        (vswap! claims conj aux)
        (boundary! rt (when (runtime-field rt :audit)
                        {:t :t02 :w (runtime-field rt :world) :scope (runtime-field rt :root)
                         :e id :kind :atom :allocation id :value payload}))
        (when (= collected (a aux 0))
          ;; The trusted allocation-wide host fact also applies to this copy.
          ;; Keep it only on extant cells; no global collection history grows.
          (put-cell-gc-receipt! rt id collected)
          (boundary! rt (when (runtime-field rt :audit)
                          {:t :source-unreachable :w (runtime-field rt :world)
                           :e id :allocation collected})))
        {:backing rt :node node :aux aux :owner (a node n-owner) :payload payload})))

(defn- allocate-managed-source! [requested value options kind]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested)
        id (keyword (str "atom-" (random-uuid)))
        payload (when (= :atom kind) {:value value :meta (:meta options)})]
    (when (or (active-operation) (active-mailbox-callback))
      (throw (ex-info "Resource callbacks cannot allocate sources" {:error :cleanup-only})))
    (locked rt
            (check-cell-caller! rt)
            (when (contains? #{:deferred :mailbox} kind) (custody-resource-ingress! rt))
            (let [frame (current-activation)
                  run (when (and frame (same-cell-world? rt (a frame 0))) (a frame 1))
                  order (if run (put frame 2 (inc (long (a frame 2)))) 0)
                  owner (selected-owner rt)
                  creator (when-not (or (root-owner? owner) (scope-owner? owner)) owner)
                  node (node! rt id kind owner)
                  aux (doto (slots 3) (put 0 id) (put 1 {}) (put 2 0))]
              (put node n-value payload) (put node n-order order)
              (when (= :deferred kind)
                (put node n-deferred (doto (slots 4) (put 0 false) (put 1 false) (put 3 (dict)))))
              (when (= :mailbox kind)
                (put node n-mailbox (doto (slots 6) (put m-messages (queue)) (put m-consumers (queue))
                                          (put m-pending (dict)) (put m-reservations (dict))
                                          (put m-protected (dict)) (put m-physical (dict)))))
              (assoc! (a (runtime-field rt :managed-cells) 0) id aux)
              (when creator (creation! creator node))
              (boundary! rt (when (runtime-field rt :audit)
                              (cond-> {:t (case kind :deferred :deferred-create :mailbox :mailbox-create :t02)
                                       :w (runtime-field rt :world) :e id :kind kind
                                       :allocation id :value payload :order order}
                                creator (assoc :r (run-id creator))
                                (scope-owner? owner) (assoc :scope (owner-id owner)))))))
    {:id id :anchor (cell-handles/allocate! id (runtime-field rt :home) collect-home-cell!)}))

(defn allocate-cell! [requested value options]
  (allocate-managed-source! requested value options :atom))

(defn cell-present? [requested id]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested)]
    (locked rt
          ;; Admission errors must propagate. An absent ordinary row alone
          ;; answers false, while cleanup access resolves its protected view.
            (if (cleanup-cell-access? rt)
              (boolean (cell-view! rt id))
              (do (check-cell-caller! rt)
                  (boolean (ordinary-cell-node rt id)))))))

(defn- read-cell-field [requested id field]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested)]
    (locked rt
            (if (cleanup-cell-access? rt)
              (let [view (cell-view! rt id)]
                (when-let [key (:cleanup view)]
                  (boundary! rt (when (runtime-field rt :audit) {:t :cleanup-cell :th :engine :cell key})))
                (get (:payload view) field))
              (do (check-cell-caller! rt)
                  (if-let [node (ordinary-cell-node rt id)]
                    (get (a node n-value) field)
                    (throw (ex-info "Released managed atom" {:error :missing-cell :id id}))))))))
(defn read-cell-value [rt id] (read-cell-field rt id :value))
(defn read-cell-meta [rt id] (read-cell-field rt id :meta))
(defn read-cell-watches [requested id]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested)]
    (locked rt
            (let [view (cell-view! rt id)]
            ;; Listener registration never shadows a following source payload.
              (when (:watch-aux view) (:watches view))))))

(defn- commit-cell-payload! [rt id view payload claims]
  (if-let [key (:cleanup view)]
    (do (put (:retained view) 1 payload)
        (boundary! rt (when (runtime-field rt :audit)
                        {:t :cleanup-cell :th :engine :cell key :value payload}))
        nil)
    (let [local (localize-cell! rt id view claims)
          listeners (a (:aux local) 1)]
      (write-source! rt (:node local) {:id id} payload)
      listeners)))

(defn swap-cell! [requested ref id f args]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested)]
    (loop []
      (let [before (retain-cell-operation! rt id)
            result
            (try
              (let [old (:value (:payload before))
                    value (apply f old args)
                    payload (assoc (:payload before) :value value)
                    _ (admit-world-switch! rt)
                    committed (locked rt
                                      (let [current (cell-view! rt id)]
                                        (when (same-cell-view? before current)
                                          [value (commit-cell-payload! rt id current payload (:claims before))])))]
                (when committed
                ;; This is a committed delivery, not a physical resource lease:
                ;; later cancellation/removal does not revoke captured watches.
                  (binding [ec/*execution-context* requested]
                    (ec/notify-listeners! ref id old value (second committed)))
                  (drain! rt))
                committed)
              (finally (release-cell-operation! rt before)))]
        (if result (first result) (recur))))))

(defn cas-cell! [requested ref id old-value new-value]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested)]
    (loop []
      (let [before (retain-cell-operation! rt id)
            result
            (try
              (if-not (identical? old-value (:value (:payload before)))
                :mismatch
                (let [payload (assoc (:payload before) :value new-value)
                      _ (admit-world-switch! rt)
                      committed (locked rt
                                        (let [current (cell-view! rt id)]
                                          (when (same-cell-view? before current)
                                            [(commit-cell-payload! rt id current payload (:claims before))])))]
                  (when committed
                    (binding [ec/*execution-context* requested]
                      (ec/notify-listeners! ref id old-value new-value (first committed)))
                    (drain! rt))
                  committed))
              (finally (release-cell-operation! rt before)))]
        (cond (= :mismatch result) false result true :else (recur))))))

(defn- edit-cell-watch! [requested id key f add?]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested)]
    (loop []
      (let [before (retain-cell-operation! rt id)
            result
            (try
              (when (:cleanup before)
                (throw (ex-info "Cleanup cannot register ordinary watches" {:error :cleanup-only :id id})))
              (let [watches (:watches before)
                  ;; Both hashing and key equality can invoke arbitrary code.
                    candidate (if add? (assoc watches key f) (dissoc watches key))
                    _ (admit-world-switch! rt)]
                (locked rt
                        (let [current (cell-view! rt id)]
                          (when (and (same-cell-view? before current)
                                     (identical? (:watch-aux before) (:watch-aux current))
                                     (identical? watches (:watches current)))
                          ;; Watches are selected-world egress, independent of
                          ;; payload COW. Removing an absent watch creates no
                          ;; registration state in a borrowed world.
                            (when (or add? (:watch-aux current))
                              (let [aux (or (:watch-aux current)
                                            (doto (slots 3) (put 0 id) (put 2 0)))]
                                (put aux 1 candidate)
                                (assoc! (a (runtime-field rt :managed-cells) 0) id aux)))
                            true))))
              (finally (release-cell-operation! rt before)))]
        (when-not result (recur))))
    nil))
(defn add-cell-watch! [rt id key f] (edit-cell-watch! rt id key f true))
(defn remove-cell-watch! [rt id key] (edit-cell-watch! rt id key nil false))

(defn- cell-in-use? [rt node aux]
  (let [id (a node n-id)]
    (or (pos? (long (a aux 2)))
        (when-let [state (a node n-deferred)] (not (empty-dict? (a state 3))))
        (when-let [control (a node n-mailbox)]
          (or (queued? (a control m-consumers))
              (not (empty-dict? (a control m-reservations))) (not (empty-dict? (a control m-physical)))))
        (any! (a node n-dependents) #(a % o-live))
        (any! (runtime-field rt :events) #(identical? node (a % 0)))
        ;; A live following world with no local row still needs this backing.
        (some (fn [world]
                (and (not (custody-data-world? world)) (not (same-cell-world? rt world))
                     (when-let [[backing _ _] (cell-backing world id)]
                       (same-cell-world? rt backing))))
              (values (runtime-field rt :family))))))

(defn- ancestor-cell-gc-pending? [rt id allocation]
  ;; Keep the local copy independent until collected ancestor storage is gone.
  ;; Removing it sooner would restore read-through and block that ancestor.
  (loop [ancestor (runtime-field rt :parent)]
    (when ancestor
      (or (= allocation (find! (a (runtime-field ancestor :managed-cells) 1) id))
          (recur (runtime-field ancestor :parent))))))

(defn- retry-world-cell-gc! [rt id]
  (let [state (runtime-field rt :managed-cells)]
    (when-let [allocation (find! (a state 1) id)]
      (let [node (find! (runtime-field rt :nodes) id)
            aux (find! (a state 0) id)
            current? (and node aux (#{:atom :deferred :mailbox} (a node n-kind)) (= allocation (a aux 0)))]
        (when (or (not current?)
                  (and (not (ancestor-cell-gc-pending? rt id allocation))
                       (not (cell-in-use? rt node aux))))
          (clear-cell-gc-receipt! rt id)
          (when current?
            (owner! rt node nil)
            (reclaim-unwanted! rt node))
          (boundary! rt (when (runtime-field rt :audit)
                          {:t :reap-source :w (runtime-field rt :world) :e id :allocation allocation})))))))

(defn- retry-family-cell-id! [rt id]
  (each! [world (values (runtime-field rt :family))]
         (when-not (custody-data-world? world)
           (let [aux-table (a (runtime-field world :managed-cells) 0)
                 aux (find! aux-table id)]
           ;; A borrowed watch registration cannot keep a retired backing
           ;; allocation or its callbacks alive after ordinary ownership exit.
             (when (and aux (nil? (find! (runtime-field world :nodes) id)))
               (let [[_ node backing-aux] (cell-backing world id)]
                 (when-not (and node backing-aux (= (a aux 0) (a backing-aux 0)))
                   (dissoc! aux-table id))))
             (retry-world-cell-gc! world id)))))

(defn- retry-cell-gc! [rt]
  ;; Ordinary publication with no dirty IDs performs no world or cell scans.
  ;; Reaping/clearing a receipt queues the ID again, so ancestor-first progress
  ;; does not depend on family iteration order or recursive boundary dispatch.
  (let [gc (:cell-gc (runtime-field rt :home))]
    (when (and (not (a gc 2)) (zero? (long (a gc 3))) (queued? (a gc 0)))
      (put gc 2 true)
      (try
        (loop []
          (when (zero? (long (a gc 3)))
            (when-let [id (pop! (a gc 0))]
              (dissoc! (a gc 1) id)
              (retry-family-cell-id! rt id)
              (recur))))
        (finally (put gc 2 false))))))

(defn- collect-home-cell! [home id]
  ;; The Cleaner registry owns only a weak home reference and this global fn.
  ;; Blocked receipts stay in world-owned metadata and retry at later boundaries.
  (let [collect (fn []
                  (let [worlds (vec (values (:worlds home)))
                        gc (:cell-gc home)]
                    ;; Publish each trusted fact separately for model replay,
                    ;; but do not reap a child before its ancestor's fact has
                    ;; been published. Otherwise deleting the child copy can
                    ;; turn it back into a following dependency on the parent.
                    (put gc 3 (inc (long (a gc 3))))
                    (try
                      (doseq [rt worlds
                              :let [aux (find! (a (runtime-field rt :managed-cells) 0) id)
                                    node (find! (runtime-field rt :nodes) id)]
                              :when (and aux node (#{:atom :deferred :mailbox} (a node n-kind)) (= id (a aux 0)))]
                        (put-cell-gc-receipt! rt id id)
                        (boundary! rt (when (runtime-field rt :audit)
                                        {:t :source-unreachable :w (runtime-field rt :world) :e id :allocation id})))
                      (finally
                        (put gc 3 (dec (long (a gc 3))))))
                    (when-let [rt (first worlds)] (retry-cell-gc! rt))))]
    #?(:clj (locking (:gate home) (collect)) :cljs (collect))))

(defn compare-and-set-signal!
  "Identity CAS, including atom-style ABA semantics. The commit and reactive
  notification are one gated operation; a failed comparison changes nothing."
  [requested source old-value new-value]
  (let [rt (execution-runtime requested)]
    (check-source! rt source)
    (let [changed? (locked rt
                           (if-let [[key cell] (cleanup-cell! rt source)]
                             (when (identical? old-value (a cell 1))
                               (put cell 1 new-value)
                               (boundary! rt (when (runtime-field rt :audit) {:t :cleanup-cell :th :engine :cell key :value new-value}))
                               true)
                             (let [node (source-node! rt source false)]
                               (when (identical? old-value (a node n-value))
                                 (write-source! rt node source new-value)
                                 true))))]
      (when changed? (drain! rt))
      (boolean changed?))))

(defn swap-signal!
  "Apply f outside the ownership gate, retrying if its input changed."
  [requested source f & args]
  (loop []
    (let [old-value (read-signal requested source)
          new-value (if (seq args) (apply f old-value args) (f old-value))]
      (if (compare-and-set-signal! requested source old-value new-value)
        new-value
        (recur)))))

(defn cancel-spin! [requested handle]
  (admit-native-effect!)
  (let [rt (execution-runtime requested)]
    (locked rt
            (check-native-caller! rt)
            (check-token! rt (:token handle))
            (let [node (find! (runtime-field rt :nodes) (:id handle)) run (when node (current node))
                  id (when run [(a node n-id) (a run r-gen)])]
              (when run (check-scope-close! rt run) (cancel! rt run))
              (boundary! rt (when (runtime-field rt :audit) {:t :t11 :w (runtime-field rt :world) :r id}))))
    (drain! rt)))

(defn join-ready?
  "Physical join observation for a run ID, root scope or world in the native profile."
  [rt scope]
  (locked rt
          (and (not-any? (fn [run]
                           (and (or (work-status? (a run r-status)) (a run r-physical))
                                (some #{scope} (or (a run r-anchor) (run-anchor rt run)))))
                         (items (a (runtime-field rt :counters) 6)))
               (not-any? #(let [run (a % z-run)]
                            (some #{scope} (or (a run r-anchor) (run-anchor rt run))))
                         (values (a (runtime-field rt :timers) 0)))
               (not-any? #(some #{scope} (a % x-anchor))
                         (when-let [profile (runtime-field rt :finalization)] (values (a profile 0)))))))

(defn release-idle! [requested]
  (admit-native-effect!)
  (let [rt (execution-runtime requested)]
    (locked rt
            (check-native-caller! rt)
            (doseq [node (vec (values (runtime-field rt :nodes)))
                    :when (and (= :spin (a node n-kind)) (a node n-complete) (not (wanted? node)))]
              (doseq [token (items (a node n-tokens))] (add! (a token t-dropped) (runtime-field rt :world)))
              (clear-members! (a node n-tokens))
              (mark! rt node))
            (boundary! rt (when (runtime-field rt :audit) {:t :t18 :w (runtime-field rt :world)})))))

(defn- run-id [run]
  (when run (if (vector? run) run [(a (a run r-node) n-id) (a run r-gen)])))
(defn- owner-id [owner]
  (cond (root-owner? owner) (:id owner)
        (scope-owner? owner) (a (owner-storage owner) s-id)
        :else (run-id owner)))
(defn- map-value [m]
  #?(:clj (into {} m)
     :cljs (let [result (volatile! {})]
             (if (instance? IDMap m)
               (.forEach (.-buckets m)
                         (fn [bucket]
                           (loop [i 0]
                             (when (< i (.-length bucket))
                               (vswap! result assoc (aget bucket i) (aget bucket (inc i)))
                               (recur (+ i 2))))))
               (.forEach m (fn [value key] (vswap! result assoc key value))))
             @result)))

(defn- global-view [rt]
  (if-let [retired (when-not *custody-frame*
                     (:custody-retired (a (runtime-field rt :counters) 11)))]
    retired
    (let [family (or (:family *custody-frame*) (runtime-field rt :family))
          worlds (values family) service (or (custody-state rt) (:service *custody-frame*))
          state (some-> service deref)
          wid (fn [world] (if (custody-data-world? world) (:world world) (runtime-field world :world)))
          lineage (fn [world] (if (custody-data-world? world) (:lineage world) (runtime-field world :lineage)))]
      {:registry (set (for [world worlds :when (and (not (custody-data-world? world))
                                                    (= :live (a (runtime-field world :lifecycle) 0)))] (wid world)))
       :known-worlds (set (map wid worlds))
       :lineages (into {} (for [world worlds] [(wid world) (lineage world)]))
       :caps (into {} (for [[id cap] (map-value (or (:caps state) (a (runtime-field rt :counters) 7)))]
                        [id (custody-cap-view cap)]))
       :custody (:custody (custody-project rt)) :records (:records (custody-project rt))
       :next-claim (:next-claim (custody-project rt)) :recovery-epoch 0 :process-live? true
       :generation-clock (into {} (mapcat (fn [world]
                                            (if (custody-data-world? world) (:generation-clock world)
                                                (for [[id n] (when-let [clock (a (runtime-field world :counters) 3)] (map-value clock))]
                                                  [[(wid world) id] n]))) worlds))})))

(defn- all-obligations [rt]
  ;; Internal graph links already own reactive registrations. Only ticket
  ;; deliveries need lookup by a host-visible registration number.
  (concat (mapcat #(items (a % r-obs)) (items (a (runtime-field rt :counters) 6)))
          (for [node (values (runtime-field rt :nodes)) ob (items (a node n-dependents))
                :when (nil? (a ob o-run))] ob)))

(defn- snapshot-live [rt]
  (locked rt
          (merge (timer-profile-view rt)
                 (when (a (runtime-field rt :managed-cells) 2)
                   {:source-gc (into {} (for [[id allocation] (map-value (a (runtime-field rt :managed-cells) 1))]
                                          [[(runtime-field rt :world) id allocation] true]))})
                 {:global (global-view rt) :cleanup-targets (custody-targets-view rt) :lineage (runtime-field rt :lineage) :root (runtime-field rt :root) :status (if (custody-world-phase rt) :sealed :live)
                  :admission (if (custody-world-phase rt) :fenced :open)
                  :seal-seq (get-in (some-> (custody-state rt) deref) [:phases (runtime-field rt :owner-root) :seal-seq])
                  :scopes (into {(runtime-field rt :root) {:kind (if (runtime-field rt :parent) :fork :world-root) :parent nil :status :open}}
                                (for [scope (when-let [state (scope-state rt)] (values (a state 0)))
                                      :let [data (owner-storage scope) parent (a data s-parent)]]
                                  [(a data s-id)
                                   (cond-> {:kind (a data s-kind) :parent (owner-id parent) :status :open}
                                     (and parent (not (root-owner? parent)) (not (scope-owner? parent))) (assoc :order (a data s-order))
                                     (a data s-origin) (assoc :origin (a data s-origin) :source-world (a data s-source-world)))]))
                  :next-scope (if-let [state (scope-state rt)] (a state 2) 0)
                  :scope-balance (if-let [state (scope-state rt)] (a state 3) 0)
                  :pins #{} :fdeps #{} :releasing #{} :principals #{}
                  :entities (into {} (for [node (values (runtime-field rt :nodes))]
                                       [(a node n-id)
                                        (cond-> {:kind (a node n-kind) :origin (or (a node n-origin) :created) :owner (owner-id (a node n-owner))
                                                 :creator (run-id (a node n-creator)) :completed? (boolean (a node n-complete))
                                                 :kept? (boolean (a node n-kept)) :result (diagnostic-value (a node n-value) (= :error (a node n-complete)))
                                                 :tokens (set (map #(a % t-id) (items (a node n-tokens)))) :key nil :order (a node n-order)}
                                          (a node n-cancelled)
                                          (assoc :cancelled-completion {:run (first (a node n-cancelled))
                                                                        :result (diagnostic-value (a node n-value) true)})
                                          (#{:atom :deferred :mailbox} (a node n-kind)) (assoc :allocation (source-allocation rt (a node n-id)))
                                          (= :deferred (a node n-kind)) (assoc :deferred (deferred-metadata (a node n-deferred)))
                                          (= :mailbox (a node n-kind)) (assoc :mailbox (mailbox-metadata (a node n-mailbox)))
                                          (some? (a node n-dirty)) (assoc :dirty? (a node n-dirty))
                                          (a node n-source-world) (assoc :source-world (:world (a node n-source-world))))]))
                  :runs (into {} (for [run (items (a (runtime-field rt :counters) 6)) :let [node (a run r-node)]]
                                   [(run-id run) (cond-> {:spin (a node n-id) :owner (owner-id (a run r-owner))
                                                          :pred (when-let [gen (a run r-pred)] [(a node n-id) gen])
                                                          :ancestors (set (map #(vector (a node n-id) %) (items (a run r-ancestors))))
                                                          :status (a run r-status) :seq (a run r-seq)
                                                          :creations (set (map #(a % n-id) (items (a run r-created))))
                                                          :spawned (set (map run-id (items (a run r-spawned))))}
                                                   (a run r-validation-lost) (assoc :validation-lost? true)
                                                   (a run r-entered) (assoc :cps-entered? true)
                                                   (a run r-finalization-seq) (assoc :finalization-sequence (a run r-finalization-seq))
                                                   (= :unwinding (a run r-status)) (assoc :retired? true :anchor (a run r-anchor))
                                                   (a run r-origin) (assoc :origin (a run r-origin) :source-world (a run r-source-world)))]))
                  :obligations (into {} (for [ob (all-obligations rt)]
                                          [[:o (a ob o-id)]
                                           (cond-> {:kind (a ob o-kind) :debtor (if-let [debtor (a ob o-debtor)]
                                                                                  [:entity (:world (a debtor n-runtime)) (a debtor n-id)]
                                                                                  [:host (a ob o-host)])
                                                    :creditor (if-let [run (a ob o-run)] [:run (runtime-field rt :world) (run-id run)] [:host :caller])
                                                    :standing? (a ob o-standing) :cont (when (a ob o-run) [:continuation [:o (a ob o-id)]])
                                                    :token nil :order (a ob o-order) :slot (a ob o-slot)}
                                             (a ob o-run) (assoc :origin (or (a ob o-origin) :created))
                                             (a ob o-timer) (assoc :timer (a (a ob o-timer) z-id))
                                             (a ob o-source-world) (assoc :source-world (a ob o-source-world))
                                             (nil? (a ob o-run)) (assoc :filter {:mode :local :origin (runtime-field rt :world)}))]))
                  :queue (mapv (fn [event]
                                 (if (custody-event? event) (custody-event-view event)
                                     (case (alength ^objects event)
                                       9 (cond-> {:mailbox-post (:id (a event 1)) :allocation (:id (a event 1))
                                                  :message-id (first (a event 3)) :value (second (a event 3)) :seq (a event 2)}
                                           (a event 5) (assoc :cell (a event 5)) (a event 7) (assoc :repost? true))
                                       7 (cond-> {:deferred-assignment (:id (a event 1)) :allocation (:id (a event 1))
                                                  :value (a event 3) :seq (a event 2)}
                                           (a event 5) (assoc :cell (a event 5)))
                                       (cond-> {:completion (a (a event 0) n-id) :debtor-world (runtime-field rt :world)
                                                :value (diagnostic-value (a event 1) (a event 3)) :seq (a event 2)}
                                         (#{:signal :atom} (a (a event 0) n-kind)) (assoc :source-change? true)))))
                               (filter (fn [event]
                                         (identical? rt (if (custody-event? event) (a event 2)
                                                            (if (#{7 9} (alength ^objects event)) (a event 0)
                                                                (a (a event 0) n-runtime)))))
                                       (items (runtime-field rt :events))))
                  :seq (a (runtime-field rt :counters) 1)
                  :serial (a (runtime-field rt :serial) 0) :clock (a (runtime-field rt :counters) 2)
                  :threads (let [run (a (runtime-field rt :thread) 0)
                                 ticket (a (runtime-field rt :thread) 4)
                                 id (if ticket (nth (a ticket x-id) 2) (run-id run))]
                             (cond-> {:host {:world (a (runtime-field rt :thread) 3) :scope nil :run nil :read-permits #{} :excl-permits []}}
                               (a (runtime-field rt :thread) 1)
                               (assoc :engine (cond-> {:world (a (runtime-field rt :thread) 2) :scope id :run id :executing? (boolean id)}
                                                id (assoc :obligation-world (a (runtime-field rt :thread) 2))
                                                (= :unwinding (some-> run (a r-status))) (assoc :retired? true)
                                                (and (= :unwinding (some-> run (a r-status)))
                                                     (not= :live (a (runtime-field rt :lifecycle) 0)))
                                                (assoc :anchor (a run r-anchor))
                                                ticket (assoc :retired? true :anchor (a ticket x-anchor) :cleanup-ticket (a ticket x-id))))))
                  :gc (mapv (fn [notification]
                              (let [target (a notification 0) token (a notification 1)]
                                {:t :t17 :w (runtime-field target :world) :e (a token t-spin) :tok (a token t-id)}))
                            (items (runtime-field rt :gc)))
                  :handles (when (runtime-field rt :tokens)
                             (into {} (for [token (items (runtime-field rt :tokens))]
                                        [(a token t-id) {:spin (a token t-spin) :reachable? (a token t-reachable)
                                                         :touched (set (items (a token t-touched))) :dropped (set (items (a token t-dropped)))}])))})))

(defn snapshot [rt]
  (locked rt
          (let [live (snapshot-live rt)]
            (if (= :live (a (runtime-field rt :lifecycle) 0)) live
                (release-view rt live)))))

(defn- fork-custody-copy!
  "Copy the supported parked host-ticket closure, then publish one affine leaf.
  Entity-debtor/resource bundles remain outside this fork profile."
  [rt world owner cap-id]
  (admit-native-effect!)
  (locked rt
          (when-not (empty-dict? (a (runtime-field rt :timers) 0))
            (throw (ex-info "Timer fork recovery is not implemented" {:error :unsupported-operation :operation :fork-timer})))
          (when (or (some #(= :mailbox (a % n-kind)) (values (runtime-field rt :nodes)))
                    (when-let [profile (runtime-field rt :finalization)]
                      (or (some #(= :mailbox (a % 0)) (values (a profile 1)))
                          (some #(= :mailbox-callback (a % x-kind)) (values (a profile 0))))))
            (throw (ex-info "Mailbox fork recovery is not implemented" {:error :unsupported-operation :operation :fork-mailbox})))
          (when (some #(= :deferred (a % n-kind)) (values (runtime-field rt :nodes)))
            (throw (ex-info "Deferred fork recovery is not implemented" {:error :unsupported-operation :operation :fork-deferred})))
          (when-let [profile (runtime-field rt :finalization)]
            (when (or (not (empty-dict? (a profile 0)))
                      (not (empty-dict? (a profile 1))) (queued? (a profile 2)))
              (throw (ex-info "Protected CPS participants require fork recovery" {:error :unsupported-finalization-fork}))))
          (when (find! (runtime-field rt :family) world)
            (throw (ex-info "World ID already used" {:world world})))
          (when (or (a (runtime-field rt :thread) 0) (queued? (runtime-field rt :events)))
            (throw (ex-info "Fork requires a parked boundary" {:world (runtime-field rt :world)})))
          (let [copies (vec (filter #(= :parked (a % r-status)) (items (a (runtime-field rt :counters) 6))))
                run-map (dict) scope-map (dict)
                scope-copies (loop [parents copies found []]
                               (let [children (vec (mapcat #(when-let [children (scope-children rt %)] (items children)) parents))]
                                 (if (empty? children) found (recur children (into found children)))))
                owners (into (set copies) scope-copies)
                selected (members)]
            (each! [run (a (runtime-field rt :counters) 6)]
                   (when (fork-busy-status? (a run r-status))
                     (throw (ex-info "Fork requires a parked boundary" {:world (runtime-field rt :world)}))))
            (doseq [run copies]
              (each! [ob (a run r-obs)]
                     (when (find! (runtime-field rt :operations) (a ob o-id))
                       (throw (ex-info "Native operations require fork recovery" {:world (runtime-field rt :world)})))
                     (when (or (a ob o-debtor) (not= :await-once (a ob o-kind)))
                       (throw (ex-info "Entity-debtor bundles are outside this slice" {:world (runtime-field rt :world)}))))
              (add! selected (a run r-node)))
            (each! [node (values (runtime-field rt :nodes))]
                   (when (or (contains? owners (a node n-owner)) (contains? owners (a node n-creator)))
                     (add! selected node)))
            (let [profile (runtime-field rt :finalization)
                  child (assoc (runtime {:audit? (boolean (runtime-field rt :audit)) :world-id world
                                         :cps-exit? (boolean profile)
                                         :on-finalization-result (when profile (a profile 4))})
                               :gate (runtime-field rt :gate) :family-id (runtime-field rt :family-id))
                  _ (vreset! (runtime-field child :arena-cell)
                             (assoc @(runtime-field child :arena-cell)
                                    :family (runtime-field rt :family) :parent rt
                                    :events (runtime-field rt :events) :hosts (runtime-field rt :hosts)
                                    :posts (runtime-field rt :posts) :ready (runtime-field rt :ready)
                                    :draining (runtime-field rt :draining) :serial (runtime-field rt :serial)
                                    :thread (runtime-field rt :thread) :gc (runtime-field rt :gc)
                                    :home (runtime-field rt :home) :audit (runtime-field rt :audit)
                                    :tokens (runtime-field rt :tokens)
                                    :lineage {:parent (runtime-field rt :world)
                                              :root (:root (runtime-field rt :lineage))
                                              :mode :following :cut nil :basis nil}))
                  node-map (dict)
                  inherited-gc (volatile! [])]
        ;; No old world version is pinned. The following child still retains
        ;; its live parent and code closures; only the parked ownership rows
        ;; are copied into child-owned mutable storage.
              (each! [node selected]
                     (let [copy (node! child (a node n-id) (a node n-kind) (runtime-field child :owner-root))]
                       (assoc! node-map node copy)
                       (fields! [field [n-complete n-kept n-value n-order n-dirty n-body n-rank n-descriptor n-cancelled]]
                                (put copy field (a node field)))
                       (when-let [aux (a node n-public-signal)]
                         (put copy n-public-signal (doto (slots 3) (put 0 (a aux 0)) (put 1 {}) (put 2 (a aux 2)))))
                       (when (= :atom (a node n-kind))
                         (assoc! (a (runtime-field child :managed-cells) 0) (a node n-id)
                                 (doto (slots 3) (put 0 (source-allocation rt (a node n-id))) (put 1 {}) (put 2 0))))
                       ;; Allocation identity follows the selected source, while
                       ;; cleanup tickets/cells/queues are fresh in the child.
                       (when (and profile (= :signal (a node n-kind)))
                         (assoc! (a (runtime-field child :finalization) 3) (a node n-id)
                                 (find! (a profile 3) (a node n-id))))
                       (when-let [allocation (when (= :atom (a node n-kind))
                                               (find! (a (runtime-field rt :managed-cells) 1) (a node n-id)))]
                         (when (= allocation (source-allocation rt (a node n-id)))
                           (vswap! inherited-gc conj [(a node n-id) allocation])))
                       (put copy n-origin :inherited)
                       (put copy n-source-world
                            {:world (runtime-field rt :world)
                             :owners (conj (or (:owners (a node n-source-world)) #{})
                                           (runtime-field rt :owner-root))})
                       (each! [token (a node n-tokens)] (add! (a copy n-tokens) token))))
              (doseq [run copies]
                (let [copy (slots 26) node (find! node-map (a run r-node))]
                  (assoc! run-map run copy)
                  (put copy r-node node) (put copy r-gen (a run r-gen))
                  (put copy r-owner (runtime-field child :owner-root)) (put copy r-pred (a run r-pred))
                  (put copy r-address (a run r-address))
                  (put copy r-finalization-seq (a run r-finalization-seq))
                  (put copy r-status :inherited) (put copy r-seq (a run r-seq)) (put copy r-reactives 0)
                  (put copy r-validation-lost (a run r-validation-lost))
                  (put copy r-origin :inherited) (put copy r-source-world (runtime-field rt :world))
                  (fields! [field [r-created r-spawned r-obs r-owned r-backlinks r-childruns r-ancestors]]
                           (put copy field empty-members))
                  (each! [gen (a run r-ancestors)] (add-run! copy r-ancestors gen))
                  (add! (a (runtime-field child :counters) 8) node)
                  (assoc! (a node n-runs) (a copy r-gen) copy)
                  (when (or (nil? (current node)) (> (long (a copy r-gen)) (long (a (current node) r-gen))))
                    (put node n-current copy) (put node n-generation (a copy r-gen)))
                  (when (runtime-field child :audit) (assoc! (a (runtime-field child :counters) 3) (a node n-id) (a node n-generation)))
                  (add! (a (runtime-field child :counters) 6) copy)))
              (when-let [source-state (scope-state rt)]
                (let [state (doto (slots 4) (put 0 (id-dict)) (put 1 (dict))
                                  (put 2 (a source-state 2)) (put 3 (count scope-copies)))]
                  (vreset! (runtime-field child :execution-scopes) state)
                  (doseq [scope scope-copies]
                    (let [source (owner-storage scope) id (a source s-id)
                          capability (ScopeCapability. (runtime-field child :owner-root) id)
                          data (doto (slots 16) (put s-id id) (put s-cap capability)
                                     (put s-kind (a source s-kind)) (put s-order (a source s-order))
                                     (put s-open true) (put s-owned (members)) (put s-runs (members))
                                     (put s-origin :inherited) (put s-source-world (runtime-field rt :world))
                                     (put 8 (into [(a source s-cap)] (a source 8))))
                          copy (ScopeOwner. data)
                          parent (or (find! run-map (a source s-parent)) (find! scope-map (a source s-parent)))]
                      (when-not parent (throw (ex-info "Inherited scope has no copied parent" {:scope id})))
                      (assoc! scope-map scope copy) (assoc! (a state 0) id copy)
                      (scope-parent! child copy parent)))))
              (each! [node selected]
                     (let [copy (find! node-map node)
                           creator (a node n-creator)]
                       (when-let [owner (or (find! run-map (a node n-owner)) (find! scope-map (a node n-owner)))]
                         (owner! child copy owner))
                       (creator! child copy (or (find! run-map creator) (run-id creator)))))
              (doseq [run copies]
                (let [copy (find! run-map run)]
                  (each! [created (a run r-created)]
                         (when-let [entity (find! node-map created)] (creation! copy entity)))
                  (each! [spawned (a run r-spawned)]
                         (when-let [descendant (find! run-map spawned)]
                           (add-run! copy r-spawned descendant) (add-run! descendant r-backlinks copy)))
                  (each! [ob (a run r-obs)]
                         (let [clone (slots 24)]
                           (fields! [field [o-id o-kind o-standing o-resolve o-reject o-order o-slot o-host o-address o-body o-signal-generation]]
                                    (put clone field (a ob field)))
                           (put clone o-run copy) (put clone o-live true)
                           (put clone o-creditor-generation (a copy r-gen)) (put clone o-creditor-node (a copy r-node))
                           (put clone o-origin :inherited) (put clone o-source-world (runtime-field rt :world))
                           (add-run! copy r-obs clone)
                           (when (reactive-kind? (a clone o-kind)) (reactive-delta! copy 1))
                           (when (= :await-once (a clone o-kind)) (assoc! (runtime-field child :deliveries) (a clone o-id) clone))
                           (let [waiters (or (find! (runtime-field child :tickets) (a clone o-host))
                                             (assoc! (runtime-field child :tickets) (a clone o-host) (members)))]
                             (add! waiters clone))))))
              (put (runtime-field child :trace-address) 0 (a (runtime-field rt :trace-address) 0))
              (reclaim! child)
              (prune-ancestry! child)
              (put (runtime-field child :counters) 1 (a (runtime-field rt :counters) 1))
              (put (runtime-field child :counters) 7 (a (runtime-field rt :counters) 7))
              (custody-publish! rt child owner cap-id)
              (assoc! (runtime-field rt :family) world child)
              (node! rt [:fork world] :fork owner)
              (each! [node (values (runtime-field child :nodes))]
                     (when (= :atom (a node n-kind))
                       (note-cell-gc-blocker-change! child (a node n-id)))
                     (each! [token (a node n-tokens)] (add! (a token t-touched) world)))
              (boundary! rt (when (runtime-field rt :audit) {:t :t19 :w (runtime-field rt :world) :v world :k cap-id
                                                             :scope (owner-id owner) :systems #{}}))
              ;; T19 first publishes the independent rows. The allocation-wide
              ;; host fact remains valid for clones made after its one-shot
              ;; callback, so publish a receipt for each surviving copied cell.
              (doseq [[id allocation] @inherited-gc
                      :let [node (find! (runtime-field child :nodes) id)]
                      :when (and node (= allocation (source-allocation child id)))]
                (put-cell-gc-receipt! child id allocation)
                (boundary! child (when (runtime-field child :audit)
                                   {:t :source-unreachable :w world :e id :allocation allocation})))
              child))))

(defn snapshot-family [rt]
  (locked rt
          (let [family (or (:family *custody-frame*) (runtime-field rt :family))
                global (global-view rt)
                environment (select-keys (snapshot rt) [:handles :threads :gc :principals :cleanup-targets])]
            (into {} (for [[id world] (map-value family)]
                       [id (if (custody-data-world? world)
                             (merge environment {:id id :status :released :lineage (:lineage world)
                                                 :release (some-> (:release-data world) deref)
                                                 :native {} :cleanup-cells {} :outside [] :global global})
                             (assoc (snapshot world) :global global))])))))

(defn storage-stats [rt]
  (locked rt
          (let [runs (a (runtime-field rt :counters) 6)
                pool (items (a (runtime-field rt :counters) 0))
                protected-operations (keep #(a % x-operation)
                                           (when-let [profile (runtime-field rt :finalization)] (values (a profile 0))))]
            {:live-runs (count! runs)
             :execution-scope-rows (if-let [state (scope-state rt)] (count (map-value (a state 0))) 0)
             :execution-scope-parent-buckets (if-let [state (scope-state rt)] (count (map-value (a state 1))) 0)
             :execution-scope-parent-memberships
             (if-let [state (scope-state rt)] (reduce + 0 (map count! (values (a state 1)))) 0)
             :execution-scope-owned-memberships
             (if-let [state (scope-state rt)]
               (reduce + 0 (map #(count! (a (owner-storage %) s-owned)) (values (a state 0)))) 0)
             :execution-scope-run-memberships
             (if-let [state (scope-state rt)]
               (reduce + 0 (map #(count! (a (owner-storage %) s-runs)) (values (a state 0)))) 0)
             :custody-live-leaves (count (filter custody-live? (values (a (runtime-field rt :counters) 7))))
             :custody-terminal-caps (count (remove custody-live? (values (a (runtime-field rt :counters) 7))))
             :custody-holder-buckets (if-let [index (a (runtime-field rt :counters) 10)] (count (map-value index)) 0)
             :custody-claims (count (:claims (some-> (custody-state rt) deref)))
             :custody-pending (count (:pending (some-> (custody-state rt) deref)))
             :custody-records (count (:records (some-> (custody-state rt) deref)))
             :custody-targets (reduce + 0 (map count (vals (:targets (some-> (custody-state rt) deref)))))
             :timer-resources (count (map-value (a (runtime-field rt :timers) 0)))
             :timer-frames (reduce + 0 (map #(count (a % z-frames)) (values (a (runtime-field rt :timers) 0))))
             :protected-operations (count protected-operations)
             :operation-registrations (reduce + 0 (map #(count (map-value (a % p-registrations))) protected-operations))
             :operation-frames (reduce + 0 (map #(count (a % p-frames)) protected-operations))
             :operation-callback-references (reduce + 0 (for [operation protected-operations
                                                              registration (values (a operation p-registrations))]
                                                          (+ (if (a registration g-resolve) 1 0)
                                                             (if (a registration g-reject) 1 0))))
             :mailbox-consumers (reduce + 0 (for [node (values (runtime-field rt :nodes)) :when (a node n-mailbox)]
                                              (+ (count (map-value (a (a node n-mailbox) m-pending)))
                                                 (count (map-value (a (a node n-mailbox) m-reservations))))))
             :mailbox-physical-frames (count (filter #(= :mailbox-callback (a % x-kind))
                                                     (when-let [profile (runtime-field rt :finalization)] (values (a profile 0)))))
             :protected-tickets (if-let [profile (runtime-field rt :finalization)] (count (map-value (a profile 0))) 0)
             :retained-cleanup-cells (if-let [profile (runtime-field rt :finalization)] (count (map-value (a profile 1))) 0)
             :source-allocation-identities (+ (count (map-value (a (runtime-field rt :managed-cells) 0)))
                                              (if-let [profile (runtime-field rt :finalization)] (count (map-value (a profile 3))) 0))
             :retired-ordinary-references
             (reduce + 0 (for [run (items runs) :when (= :unwinding (a run r-status))]
                           (+ (count (filter some? (map #(a run %) [r-owner r-pred r-cancel-cont])))
                              (reduce + 0 (map #(count! (a run %)) [r-created r-spawned r-obs r-owned r-backlinks r-childruns])))))
             :idle-body-references
             (count (for [node (values (runtime-field rt :nodes))
                          :when (and (= :spin (a node n-kind)) (a node n-complete)
                                     (nil? (current node)) (a node n-body))] node))
             :liveness-scratch-references
             (let [live (runtime-field rt :liveness)]
               (+ (count! (a live 2)) (count! (a live 3))
                  #?(:clj (.size ^java.util.ArrayDeque (a live 4))
                     :cljs (alength (.toArray (a live 4))))
                  #?(:clj (.size ^java.util.Map (a live 5))
                     :cljs (.-size (a live 5)))))
             :stale-liveness-references
             (let [indexed? #(identical? % (find! (runtime-field rt :nodes) (a % n-id)))]
               (+ (count (remove indexed? (items (a (runtime-field rt :liveness) 1))))
                  (reduce + 0 (for [node (values (runtime-field rt :nodes))]
                                (count (remove indexed? (concat (items (a node n-links))
                                                                (items (a node n-link-buffer))
                                                                (items (a node n-supporters)))))))))
             :ancestry-references (reduce + 0 (map #(count! (a % r-ancestors)) (items runs)))
             :pooled-runs (count pool)
             :pooled-references
             (reduce + 0 (for [run pool]
                           (+ (count (filter some? (map #(a run %) [r-node r-owner r-pred r-anchor r-exit r-cancel-cont r-address])))
                              (reduce + 0 (map #(count! (a run %))
                                               [r-created r-spawned r-obs r-owned r-backlinks r-childruns r-ancestors])))))
             :orphan-creation-links
             (count (for [node (values (runtime-field rt :nodes)) creator (items (a node n-created-by))
                          :when (not (has? runs creator))] creator))
             :scratch-references (count (filter some? (seq (a (runtime-field rt :counters) 4))))
             :stale-queue-references
             #?(:clj 0
                :cljs (reduce + 0 (map #(.staleReferences %)
                                       (cond-> [(runtime-field rt :events) (runtime-field rt :hosts) (runtime-field rt :work) (runtime-field rt :posts) (runtime-field rt :gc)
                                                (a (runtime-field rt :counters) 0)]
                                         (runtime-field rt :audit) (conj (a (runtime-field rt :counters) 9))
                                         (runtime-field rt :finalization) (conj (a (runtime-field rt :finalization) 2))))))})))

;; Public computation descriptors are weak node metadata, never token payloads.
(defn- weak-descriptor [descriptor]
  (when descriptor
    #?(:clj (java.lang.ref.WeakReference. descriptor) :cljs (js/WeakRef. descriptor))))
(defn- descriptor-value [reference]
  (when reference #?(:clj (.get ^java.lang.ref.WeakReference reference) :cljs (.deref reference))))

(defn- same-public-capture? [a b]
  (or (identical? a b)
      #?(:clj (and (or (number? a) (char? a) (keyword? a) (symbol? a) (boolean? a))
                   (.equals ^Object a b))
         :cljs (cond (number? a) (and (number? b) (.is js/Object a b))
                     (or (keyword? a) (symbol? a)) (= a b)
                     :else false))))

(defn- public-captures-changed? [old new]
  (or (not= (set (keys old)) (set (keys new)))
      (boolean (some (fn [[k value]] (not (same-public-capture? value (get old k)))) new))))

(defn- check-computation-caller! [rt]
  (world-open! rt)
  (when-let [frame (current-activation)]
    (when (identical? (runtime-field rt :gate) (runtime-field (a frame 0) :gate))
      (check-running! (a frame 1)))))

(defn- computation-witness [rt id]
  (let [node (find! (runtime-field rt :nodes) id)]
    {:node node :generation (when node (some-> (current node) (a r-gen)))
     :reference (when node (a node n-descriptor))
     :completed? (boolean (when node (a node n-complete)))}))

(defn- computation-current? [rt id witness]
  (let [node (find! (runtime-field rt :nodes) id)]
    (and (identical? node (:node witness))
         (= (:generation witness) (when node (some-> (current node) (a r-gen))))
         (identical? (:reference witness) (when node (a node n-descriptor))))))

(defn- check-public-token! [rt token id]
  (check-token! rt token)
  (when-not (and (a token t-reachable) (= id (a token t-spin)))
    (throw (ex-info "Public computation capability is unavailable"
                    {:error :unreachable-handle :id id}))))

(defn- prepare-computation!
  ([rt id body construction?] (prepare-computation! rt id body construction? nil))
  ([rt id body construction? token]
   (let [descriptor (::rtp/computation (meta body))]
     (loop []
       (let [[witness previous-descriptor]
             (locked rt
                     (check-computation-caller! rt)
                     (selected-owner rt)
                     (when token (check-public-token! rt token id))
                     (when (and (nil? (find! (runtime-field rt :nodes) id)) (parent-node rt id))
                       (throw (ex-info "Foreign invocation is outside this slice" {:id id})))
                     (let [witness (computation-witness rt id)]
                       [witness (descriptor-value (:reference witness))]))
            ;; Map traversal and scalar equality may invoke user code. Neither
            ;; comparison nor WeakRef construction executes under the gate.
             changed? (and (:node witness)
                           (or (:reference witness) (:generation witness)
                               (:completed? witness))
                           (or (nil? previous-descriptor)
                               (and construction? (= :resource (:kind descriptor)))
                               (public-captures-changed? (:captured-locals previous-descriptor)
                                                         (:captured-locals descriptor))))
             reference (if (identical? previous-descriptor descriptor)
                         (:reference witness) (weak-descriptor descriptor))
             committed
             (locked rt
                     (check-computation-caller! rt)
                     (selected-owner rt)
                     (when token (check-public-token! rt token id))
                     (when (computation-current? rt id witness)
                       (when-let [node (:node witness)]
                         (when changed?
                           (put node n-dirty true)
                           (when-let [run (current node)] (put run r-validation-lost true))
                           (boundary! rt (when (runtime-field rt :audit)
                                           {:t :invalidate-computation :w (runtime-field rt :world) :e id})))
                         (put node n-descriptor reference))
                       (assoc witness :reference (when (:node witness) reference)
                              :prepared-reference reference)))]
         (if committed committed (recur)))))))

(defn- enter-public-computation! [rt id body]
  (let [node (find! (runtime-field rt :nodes) id)
        run (when node (current node))]
    (when (and run (not= :unwinding (a run r-status)) (a node n-dirty)
               (or (not (work-status? (a run r-status))) (a run r-validation-lost)))
      ;; Constructor invalidation is lazy. Entry is an explicit cold T09,
      ;; retaining incoming observers while dropping the old outgoing suffix.
      (put node n-body body)
      (reenter! rt node nil :dirty)
      (boundary! rt (when (runtime-field rt :audit)
                      {:t :t09 :w (runtime-field rt :world) :e id :cause :dirty :order -1})))))

(defn- observe-public! [rt target id body success failure mode]
  (let [token (portable-token! rt target id false)]
    (loop []
      (let [witness (prepare-computation! rt id body false token)
            observation
            (locked rt
                    (check-computation-caller! rt)
                    (check-public-token! rt token id)
                    (when (computation-current? rt id witness)
                      (enter-public-computation! rt id body)
                      (let [owner (selected-owner rt)
                            node (or (find! (runtime-field rt :nodes) id) (node! rt id :spin owner))
                            cached? (and (a node n-complete) (not (a node n-dirty))
                                         (not (work-status? (some-> (current node) (a r-status)))))]
                        (when-not (a node n-descriptor) (put node n-descriptor (:prepared-reference witness)))
                        (when-not (a node n-owner) (owner! rt node owner))
                        (touch! rt node token)
                        (when-not (or cached? (work-status? (some-> (current node) (a r-status))))
                          (put node n-body body)
                          (start! rt node owner false))
                        (let [ob (ob! rt mode node nil 0 nil nil)]
                          (put ob o-success success) (put ob o-failure failure)
                          (when cached?
                            (push! (runtime-field rt :hosts)
                                   (doto (slots 2)
                                     (put 0 (a ob (if (= :error (a node n-complete)) o-failure o-success)))
                                     (put 1 (a node n-value))))
                            (when (or (= :deref mode) (not (reactive? (current node)))) (end-ob! rt ob)))
                          (boundary! rt (when (runtime-field rt :audit)
                                          (cond-> {:t :t04 :w (runtime-field rt :world) :e id :tok (a token t-id) :mode mode}
                                            (not (root-owner? owner)) (assoc :scope (owner-id owner)))))
                          {:ob ob :cached? cached?}))))]
        (if observation observation (recur))))))

(defn- host-callback-scope [requested f value]
  #?(:clj
     (let [values (object-array 10)]
       (aset values 0 #'ec/*execution-context*) (aset values 1 requested)
       (aset values 2 #'ec/*spin-id*) (aset values 4 #'ec/*run-gen*)
       (aset values 6 #'ec/*lifetime-run*) (aset values 8 #'ec/*owner-scope*)
       (push-thread-bindings (clojure.lang.PersistentArrayMap. values))
       (try (with-activation nil (f value)) (finally (pop-thread-bindings))))
     :cljs
     (binding [ec/*execution-context* requested ec/*spin-id* nil ec/*run-gen* nil
               ec/*lifetime-run* nil ec/*owner-scope* nil]
       (with-activation nil (f value)))))

(defn- invoke-public-computation! [requested target id body resolve reject mode]
  (try
    (admit-world-switch! requested)
    (let [rt (canonical-runtime requested)
          in-call (volatile! true)
          thread #?(:clj (Thread/currentThread) :cljs nil)
          outer-trampoline? (cps/in-trampoline?)
          outcome (volatile! nil)
          callback
          (fn [failed? f]
            (fn [value]
              (let [inline? (and @in-call #?(:clj (identical? thread (Thread/currentThread)) :cljs true))
                    receipt (when (and inline? (nil? @outcome))
                              (let [ret (volatile! nil)] (vreset! outcome [failed? value ret]) ret))
                    ret (host-callback-scope
                         requested
                         (fn [value]
                           (if (and inline? outer-trampoline?)
                             (cps-runtime/call-in-trampoline
                              (fn [token] (binding [cps/*in-trampoline* token]
                                            (cps/invoke-continuation f value))))
                             (binding [cps/*in-trampoline* false] (cps/invoke-continuation f value))))
                         value)]
                (when receipt (vreset! receipt ret))
                ret)))
          observation (observe-public! rt target id body (callback false resolve) (callback true reject) mode)]
      (try
        (drain! rt)
        (if-let [[failed? value ret] @outcome]
          (cond
            (cps-runtime/thunk? @ret) @ret
            (and failed? (:cached? observation))
            (if (= :org.replikativ.spindel.spin.core/spin-cancelled (:type (ex-data value))) nil (throw value))
            failed? nil
            :else value)
          :org.replikativ.spindel.spin/incomplete)
        (finally (vreset! in-call false))))
    (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))

(defn computation-result [requested target id]
  (try
    (admit-world-switch! requested)
    (let [rt (canonical-runtime requested)]
      (locked rt
              (check-computation-caller! rt)
              (when-let [node (find! (runtime-field rt :nodes) id)]
                (when (a node n-complete)
                  {:variant (if (= :error (a node n-complete)) :error :ok)
                   :payload (a node n-value)
                   :clean? (and (not (a node n-dirty))
                                (not (work-status? (some-> (current node) (a r-status)))))}))))
    (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))

(defn cancel-computation! [requested target id body reason]
  (try
    (admit-world-switch! requested)
    (let [rt (canonical-runtime requested)
          _ (locked rt
                    (when-let [node (find! (runtime-field rt :nodes) id)]
                      (doseq [run (values (a node n-runs))] (check-scope-close! rt run))))
          token (portable-token! rt target id false)]
      (loop []
        (let [witness (prepare-computation! rt id body false token)
              committed?
              (locked rt
                      (check-computation-caller! rt)
                      (check-public-token! rt token id)
                      (when (computation-current? rt id witness)
                        (let [node (or (find! (runtime-field rt :nodes) id)
                                       (node! rt id :spin (runtime-field rt :owner-root)))]
                          (when-not (a node n-descriptor) (put node n-descriptor (:prepared-reference witness)))
                          (touch! rt node token)
                          (when-not (a node n-cancelled)
                            (let [runs (vec (sort-by #(a % r-gen) > (values (a node n-runs))))
                                  cancelled-run (run-id (current node))
                                  dirty? (boolean (or (a node n-dirty)
                                                      (some-> (current node) (a r-validation-lost))))
                                  cancellation {:node node :reason reason}]
                              (doseq [run runs] (check-scope-close! rt run))
                              ;; Publish provenance before retiring anything:
                              ;; finally and incoming callbacks observe this
                              ;; first result, including pre-invocation cancel.
                              (put node n-cancelled [cancelled-run])
                              (put node n-complete :error) (put node n-value reason)
                              (drop-node-events! rt node)
                              (doseq [run runs]
                                (when-let [ticket (a run r-exit)] (install-cancel-reason! ticket cancellation))
                                (retire! rt run cancellation))
                              (doseq [ob (sort-by #(a % o-id) (seq (copy-items (a node n-dependents))))]
                                (reject-dependent! rt ob cancellation))
                              ;; Raw lifetime teardown may dirty owned graphs;
                              ;; preserve only the target's prior invalidation.
                              (put node n-dirty dirty?)))
                          (boundary! rt (when (runtime-field rt :audit)
                                          {:t :cancel-computation :w (runtime-field rt :world)
                                           :e id :tok (a token t-id) :value (diagnostic-value reason true)}))
                          true)))]
          (when-not committed? (recur))))
      (drain! rt))
    (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil))))

(defn deref-computation! [requested target id body timeout-ms timeout-val]
  #?(:cljs (throw (js/Error. "Blocking deref is unsupported in ClojureScript"))
     :clj
     (try
       (admit-world-switch! requested)
       (let [rt (canonical-runtime requested)]
         (when (or (current-activation) @(runtime-field rt :draining))
           (throw (ex-info "Cannot block while the native engine is executing" {:error :blocking-engine-wait})))
         (let [result (promise)
               timeout (Object.)
               settle (fn [variant value]
                        (host-callback-scope requested
                                             #(deliver result {:variant variant :payload %}) value))
               observation (observe-public! rt target id body #(settle :ok %) #(settle :error %) :deref)]
           (drain! rt)
           (let [outcome (if (pos? timeout-ms) (deref result timeout-ms timeout) @result)]
             (cond
               (identical? timeout outcome)
               (do (locked rt
                           (end-ob! rt (:ob observation))
                           (boundary! rt (when (runtime-field rt :audit)
                                           {:t :withdraw-deref :w (runtime-field rt :world)
                                            :o [:o (a (:ob observation) o-id)]})))
                   timeout-val)
               (= :error (:variant outcome)) (throw (:payload outcome))
               :else (:payload outcome)))))
       (finally (java.lang.ref.Reference/reachabilityFence target)))))

(defn await-public-computation! [requested target id body _caller-id _source-loc resolve reject]
  (if (and id body)
    (try
      (admit-world-switch! requested)
      (let [rt (canonical-runtime requested) frame (current-activation)]
        (when-not (and frame (same-cell-world? rt (a frame 0)))
          (throw (ex-info "Computation await requires the selected native activation"
                          {:error :unsupported-operation :operation :await-outside-activation})))
        (let [token (portable-token! rt target id false)
              resume-resolve (cps-runtime/scope-continuation resolve)
              resume-reject (cps-runtime/scope-continuation reject)]
          (loop []
            (let [witness (prepare-computation! rt id body false token)
                  committed?
                  (locked rt
                          (check-computation-caller! rt)
                          (check-public-token! rt token id)
                          (when (computation-current? rt id witness)
                            (enter-public-computation! rt id body)
                            (let [run (a frame 1)
                                  order (put frame 2 (inc (long (a frame 2))))
                                  ob (register-await! rt run order id token body resume-resolve resume-reject
                                                      (:prepared-reference witness))]
                              (when-let [node (find! (runtime-field rt :nodes) id)]
                                (when-not (a node n-descriptor) (put node n-descriptor (:prepared-reference witness))))
                              ob)))]
              (if committed?
                (when (= :consumed (a committed? o-slot))
                  (deliver-value! resolve reject (a committed? o-value) (a committed? o-delivery-error)))
                (recur))))))
      (finally #?(:clj (java.lang.ref.Reference/reachabilityFence target) :cljs nil)))
    (cond
      (satisfies? rtp/PCompletion target)
      (lifecycle-await! requested target resolve reject)
      (satisfies? rtp/PMailbox target)
      (await-public-mailbox! requested target resolve reject false)
      (satisfies? rtp/PMailboxNext target)
      (let [mailbox (rtp/mailbox-next-target target)]
        (await-public-mailbox! requested mailbox (fn [value] (cps/invoke-continuation resolve [value mailbox])) reject false))
      (satisfies? rtp/PDeferred target)
      (await-public-deferred! requested target resolve reject)
      :else
      (throw (ex-info "Native await requires a typed computation target"
                      {:error :unsupported-operation :operation :await-resource})))))

(defn await-public-finalization! [requested operation _caller-id _source-loc resolve reject]
  (when-not (ifn? operation)
    (throw (ex-info "Protected finalization requires an async thunk" {:error :invalid-finalization-operation})))
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) frame (current-activation)]
    (when-not (and frame (same-cell-world? rt (a frame 0)))
      (throw (ex-info "Protected finalization requires the selected native activation"
                      {:error :unsupported-operation :operation :finalization-outside-activation})))
    (await-finalization-effect!
     (fn [_r _j]
       (start-protected-operation! rt operation))
     resolve reject
     (cps-runtime/scope-continuation resolve) (cps-runtime/scope-continuation reject))))

;; These descriptors contain only global functions. Scope capture stores pure
;; lexical bindings; the selected runner supplies world and generation authority.
(defn- capture-public-scope [] (ec/capture-context-scope ec/*execution-context*))
(defn- restore-public-scope [captured] (ec/restore-context-scope captured ec/*execution-context*))
(defn- bind-public-scope [value f]
  #?(:clj
     (let [values (object-array 2)]
       (aset values 0 #'ec/*execution-context*) (aset values 1 value)
       (push-thread-bindings (clojure.lang.PersistentArrayMap. values))
       (try (f) (finally (pop-thread-bindings))))
     :cljs (binding [ec/*execution-context* value] (f))))

(def ^:private public-context-descriptor
  [capture-public-scope restore-public-scope bind-public-scope])
(def ^:private public-context-frame
  {'org.replikativ.spindel.engine.core/*execution-context* public-context-descriptor})

(defn- public-scope-frame []
  (let [frame cps-runtime/*scope-frame*]
    (cond
      (identical? public-context-descriptor
                  (get frame 'org.replikativ.spindel.engine.core/*execution-context*)) frame
      (empty? frame) public-context-frame
      :else (assoc frame 'org.replikativ.spindel.engine.core/*execution-context* public-context-descriptor))))

(defn- public-slice! [rt run ticket cold-body f]
  (let [[id generation] (if run (run-id run) (some-> ticket (a x-id) (nth 2)))
        scope (:spin-scope (::rtp/computation (meta cold-body)))
        context (if (seq scope) (update rt :bindings merge scope) rt)
        run-gen (when id [id generation])
        owner-scope (when id [:run (runtime-field rt :world) id generation])
        scope-frame (public-scope-frame)]
    #?(:clj
       (let [values (object-array 12)]
         ;; This input map is private and immutable after construction. Official
         ;; push/pop still creates six fresh binding boxes on every entry.
         (aset values 0 #'ec/*execution-context*) (aset values 1 context)
         (aset values 2 #'ec/*spin-id*) (aset values 3 id)
         (aset values 4 #'ec/*run-gen*) (aset values 5 run-gen)
         (aset values 6 #'ec/*lifetime-run*) (aset values 7 generation)
         (aset values 8 #'ec/*owner-scope*) (aset values 9 owner-scope)
         (aset values 10 #'cps-runtime/*scope-frame*) (aset values 11 scope-frame)
         (push-thread-bindings (clojure.lang.PersistentArrayMap. values))
         (try (f) (finally (pop-thread-bindings))))
       :cljs
       (binding [ec/*execution-context* context ec/*spin-id* id
                 ec/*run-gen* run-gen ec/*lifetime-run* generation
                 ec/*owner-scope* owner-scope cps-runtime/*scope-frame* scope-frame]
         (f)))))

;; Public signal values use the ordinary lifetime source row. Only interval
;; receipts and egress listeners are additional representation state:
;; aux = [immutable value packet, immutable watches, allocation capability].
;; Neither the public reference nor this capability retains a runtime.
(defn register-public-signal! [requested ref]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested)
        value (delta/wrap-deltaable (:initial-value ref))
        packet {:snapshot value :old-snapshot nil :deltas nil
                :deltaable? (delta/deltaable? value) :generation 0}
        source (locked rt
                       (check-computation-caller! rt)
                       (let [frame (current-activation)
                             source (if (and frame (not (same-cell-world? rt (a frame 0))))
                                      (let [owner (selected-owner rt)]
                                        (with-activation nil
                                          (binding [ec/*owner-scope* (when-not (root-owner? owner)
                                                                       (owner-capability rt owner))]
                                            (allocate-source! rt (:id ref) value))))
                                      (allocate-source! rt (:id ref) value))
                             node (source-node! rt source false)
                             aux (or (a node n-public-signal)
                                     (put node n-public-signal
                                          (doto (slots 3) (put 0 packet) (put 1 {}) (put 2 source))))]
                         (a aux 2)))]
    (with-meta ref (assoc (meta ref) ::rtp/signal-source source))))

(defn- public-signal-source! [rt ref]
  (let [source (::rtp/signal-source (meta ref))]
    (when-not (and source (= (:id ref) (:id source)))
      (throw (ex-info "Signal has no allocation in the selected native engine"
                      {:error :unknown-source :id (:id ref)})))
    (check-source! rt source)
    source))

(defn- public-signal-view! [rt source]
  (if-let [[key cell] (cleanup-cell! rt source)]
    {:cleanup key :cell cell :value (a cell 1)}
    (do (check-cell-caller! rt)
        (let [node (source-node! rt source false)
              aux (a node n-public-signal)]
          (when-not (and aux (identical? source (a aux 2)))
            (throw (ex-info "Released public signal allocation" {:error :released-source :id (:id source)})))
          {:node node :aux aux :packet (a aux 0) :value (a node n-value)}))))

(defn- same-public-signal-view? [before current]
  (if (:cleanup before)
    (and (= (:cleanup before) (:cleanup current))
         (identical? (:cell before) (:cell current))
         (identical? (:value before) (:value current)))
    (and (nil? (:cleanup current))
         (identical? (:node before) (:node current))
         (identical? (:packet before) (:packet current)))))

(defn public-signal-value [requested ref]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) source (public-signal-source! rt ref)]
    (locked rt
            (let [view (public-signal-view! rt source)]
              (when (:cleanup view)
                (boundary! rt (when (runtime-field rt :audit)
                                {:t :cleanup-cell :th :engine :cell (:cleanup view)})))
              (:value view)))))

(defn public-signal-state [requested ref]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) source (public-signal-source! rt ref)]
    (locked rt
            (let [view (public-signal-view! rt source)]
              (if (:cleanup view)
                (do (boundary! rt (when (runtime-field rt :audit)
                                    {:t :cleanup-cell :th :engine :cell (:cleanup view)}))
                    (nodes/->signal-node (:value view) nil nil false #{} 0))
                (let [packet (:packet view)
                      observers (set (keep #(when-let [run (a % o-run)] (a (a run r-node) n-id))
                                           (items (a (:node view) n-dependents))))]
                  (nodes/->signal-node (:snapshot packet) (:old-snapshot packet) (:deltas packet)
                                       (:deltaable? packet) observers (:generation packet))))))))

(defn- signal-packet [view new-value]
  ;; Delta extraction, clearing and equality may dispatch into application code.
  ;; Prepare the entire immutable receipt outside the ownership gate.
  (let [deltas (delta/get-deltas new-value)
        clean (delta/clear-deltas new-value)]
    {:snapshot clean :old-snapshot (:value view) :deltas deltas
     :deltaable? (:deltaable? (:packet view))
     :generation (inc (long (or (:generation (:packet view)) 0)))}))

(defn- commit-public-signal! [rt source current packet publish?]
  (if (:cleanup current)
    (do (put (:cell current) 1 (:snapshot packet))
        (boundary! rt (when (runtime-field rt :audit)
                        {:t :cleanup-cell :th :engine :cell (:cleanup current) :value (:snapshot packet)}))
        nil)
    (let [aux (:aux current) watches (a aux 1)]
      (put aux 0 packet)
      (write-source! rt (:node current) source (:snapshot packet) publish?)
      watches)))

(defn swap-public-signal! [requested ref f args publish? committed-hook observe-change?]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) source (public-signal-source! rt ref)]
    (loop []
      (let [before (locked rt (public-signal-view! rt source))
            packet (signal-packet before (apply f (:value before) args))
            changed? (when observe-change? (not= (:value before) (:snapshot packet)))
            _ (admit-world-switch! rt)
            committed (locked rt
                              (let [current (public-signal-view! rt source)]
                                (when (same-public-signal-view? before current)
                                  [(commit-public-signal! rt source current packet publish?)])))]
        (if committed
          (do (when committed-hook (committed-hook))
              (binding [ec/*execution-context* requested]
                (ec/notify-listeners! ref (:id source) (:value before) (:snapshot packet) (first committed)))
              (when publish? (drain! rt))
              {:value (:snapshot packet) :changed? changed?})
          (recur))))))

(defn cas-public-signal! [requested ref old-value new-value publish?]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) source (public-signal-source! rt ref)]
    (loop []
      (let [before (locked rt (public-signal-view! rt source))]
        (if-not (identical? old-value (:value before))
          false
          (let [packet (signal-packet before new-value)
                _ (admit-world-switch! rt)
                committed (locked rt
                                  (let [current (public-signal-view! rt source)]
                                    (when (same-public-signal-view? before current)
                                      [(commit-public-signal! rt source current packet publish?)])))]
            (if committed
              (do (binding [ec/*execution-context* requested]
                    (ec/notify-listeners! ref (:id source) old-value (:snapshot packet) (first committed)))
                  (when publish? (drain! rt))
                  true)
              (recur))))))))

(defn clear-public-signal-deltas! [requested ref]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) source (public-signal-source! rt ref)]
    (locked rt
            (check-computation-caller! rt)
            (let [view (public-signal-view! rt source) aux (:aux view)]
              (put aux 0 (assoc (:packet view) :deltas nil)))))
  nil)

(defn public-signal-watches [requested ref]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) source (public-signal-source! rt ref)]
    (locked rt
            (check-computation-caller! rt)
            (a (:aux (public-signal-view! rt source)) 1))))

(defn edit-public-signal-watch! [requested ref key f add?]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) source (public-signal-source! rt ref)]
    (loop []
      (let [[before watches] (locked rt
                                     (check-computation-caller! rt)
                                     (let [view (public-signal-view! rt source)] [view (a (:aux view) 1)]))
            candidate (if add? (assoc watches key f) (dissoc watches key))
            _ (admit-world-switch! rt)
            committed? (locked rt
                               (check-computation-caller! rt)
                               (let [current (public-signal-view! rt source)]
                                 (when (and (same-public-signal-view? before current)
                                            (identical? watches (a (:aux current) 1)))
                                   (put (:aux current) 1 candidate)
                                   true)))]
        (when-not committed? (recur)))))
  ref)

(defn publish-public-signals! [requested ids]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) ids (vec (distinct ids))]
    (locked rt
            (check-computation-caller! rt)
            ;; Preflight the whole publication before the first event is seated.
            (let [nodes (mapv (fn [id]
                                (let [node (find! (runtime-field rt :nodes) id)]
                                  (when-not (and node (a node n-owner) (a node n-public-signal))
                                    (throw (ex-info "Released public signal" {:error :released-source :id id})))
                                  node)) ids)]
              (doseq [node nodes]
                (enqueue-source! rt node (a node n-value))
                (boundary! rt (when (runtime-field rt :audit)
                                (cond-> {:t :signal-publish :w (runtime-field rt :world) :e (a node n-id)}
                                  (current-activation) (assoc :th :engine)))))))
    (drain! rt))
  nil)

(defn track-public-signal! [requested ref _caller-id _source-loc resolve reject]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) source (public-signal-source! rt ref)
        frame (current-activation)]
    (when-not (and frame (same-cell-world? rt (a frame 0)))
      (throw (ex-info "Signal tracking requires the selected native activation"
                      {:error :unsupported-operation :operation :track-outside-activation})))
    (track-id-effect! (:id source) resolve reject
                      (cps-runtime/scope-continuation resolve)
                      (cps-runtime/scope-continuation reject) source)))

;; Deferred synchronization uses a managed source allocation and the engine's
;; ordinary one-shot obligations. Its private control array is
;; [claimed?, assigned?, value, protected registrations]. No pending closure
;; collection lives in an application RuntimeAtom.
(defn- deferred-metadata [control]
  {:claimed? (boolean (a control 0))
   :protected (into {} (for [registration (values (a control 3))]
                         [(a registration g-id)
                          {:operation (a (a registration g-operation) p-id)
                           :sequence (second (a (a registration g-operation) p-id))}]))})

(defn create-public-deferred! [requested _public-id]
  (let [rt (canonical-runtime requested)
        allocation (allocate-managed-source! requested nil {} :deferred)]
    (->DeferredRef (:id allocation) (runtime-field rt :family-id) (:anchor allocation))))

(defn- deferred-reference! [rt target]
  (let [ref (rtp/deferred-payload target)]
    (when-not (and (instance? DeferredRef ref)
                   (identical? (runtime-field rt :family-id) (:family ref)))
      (throw (ex-info "Deferred belongs to another engine or family" {:error :unknown-deferred})))
    ref))

(defn- deferred-retained [rt id ticket]
  (when-let [profile (runtime-field rt :finalization)]
    (first (for [[key cell] (map-value (if ticket (a ticket x-cells) (a profile 1)))
                 :when (and (= id (nth key 2)) (= :deferred (a cell 0))
                            (= id (a cell 3)) (pos? (count! (a cell 2))))]
             {:cell cell :key key :control (a cell 4)}))))

(defn- deferred-ticket [rt]
  (when-let [frame (current-activation)]
    (when (same-cell-world? rt (a frame 0))
      (or (some-> (active-operation) (a p-ticket))
          (a frame 8) (some-> (a frame 1) (a r-exit))))))

(defn- deferred-view! [rt ref purpose]
  (let [id (:id ref) frame (current-activation)
        cleanup? (cleanup-cell-access? rt)
        ticket (when (or cleanup? (active-operation)) (deferred-ticket rt))
        node (find! (runtime-field rt :nodes) id)
        aux (find! (a (runtime-field rt :managed-cells) 0) id)
        live? (and node aux (= :deferred (a node n-kind))
                   (a node n-owner) (= id (a aux 0)))
        retained (when (or cleanup? (not live?)) (deferred-retained rt id ticket))]
    (when-not (= :assign purpose)
      (when-not (or (= :protect purpose) cleanup?
                    (and (= :request purpose) (nil? frame) retained (not live?)))
        (check-cell-caller! rt)))
    (when (and cleanup? (not= :protect purpose))
      (when-not (and ticket (or (active-operation) (= :claimed (a ticket x-phase))) retained)
        (throw (ex-info "Deferred is outside the retained cleanup capability"
                        {:error :missing-cleanup-cell :id id}))))
    (when (and retained (not live?) frame (same-cell-world? rt (a frame 0))
               (not cleanup?) (not (#{:assign :protect} purpose)))
      (let [ticket (deferred-ticket rt)]
        (when-not (and ticket (has? (a (:cell retained) 2) ticket))
          (throw (ex-info "Ordinary execution has no retained Deferred authority"
                          {:error :cleanup-only :id id})))))
    (cond
      (and retained (or cleanup? (not live?))
           (or cleanup? (active-operation) (#{:request :assign :protect} purpose))) (assoc retained :node nil :aux nil)
      live? {:node node :aux aux :control (a node n-deferred)}
      (and retained (#{:request :assign :protect} purpose)) retained
      (= :assign purpose) nil
      :else (throw (ex-info "Released Deferred allocation" {:error :missing-deferred :id id})))))

(defn- deferred-action [rt ref view operation]
  (cond-> {:t operation :w (runtime-field rt :world) :e (:id ref) :allocation (:id ref)}
    (:key view) (assoc :cell (:key view))
    (when-let [frame (current-activation)] (same-cell-world? rt (a frame 0))) (assoc :th :engine)))

(defn read-public-deferred [requested target]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) ref (deferred-reference! rt target)]
    (locked rt
            (let [view (deferred-view! rt ref :read) control (:control view)]
              (when (:key view)
                (boundary! rt (when (runtime-field rt :audit)
                                {:t :cleanup-cell :th :engine :cell (:key view)})))
              {:assigned? (boolean (a control 1)) :value (a control 2)}))))

(defn- request-deferred! [requested target value claim?]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) ref (deferred-reference! rt target)
        accepted? (locked rt
                          (let [view (deferred-view! rt ref :request) control (:control view)
                                accepted? (or (not claim?) (not (a control 0)))]
                            (when accepted?
                              (when claim? (put control 0 true))
                              (let [aux (:aux view)
                                    sequence (put (runtime-field rt :counters) 2
                                                  (inc (max (long (a (runtime-field rt :counters) 1))
                                                            (long (a (runtime-field rt :counters) 2)))))
                                    event (doto (slots 7)
                                            (put 0 rt) (put 1 ref) (put 2 sequence) (put 3 value)
                                            (put 4 :deferred-assignment) (put 5 (:key view)) (put 6 aux))]
                                (when aux (put aux 2 (inc (long (a aux 2)))))
                                (push! (runtime-field rt :events) event)))
                            (boundary! rt (when (runtime-field rt :audit)
                                            (assoc (deferred-action rt ref view :deferred-request)
                                                   :value value :claim? claim?)))
                            accepted?))]
    (drain! rt)
    accepted?))

(defn claim-public-deferred! [requested target value]
  (boolean (request-deferred! requested target value true)))
(defn deliver-public-deferred! [requested target value]
  (request-deferred! requested target value false)
  value)

;; Protected operations are participants of an outer wait, not computations.
;; Only their terminal capabilities settle the outer ticket. Deferred callbacks
;; execute on a serial lane with their supplied lexical scope and payload rights.
(defn- operation-action [rt operation kind]
  {:t kind :w (runtime-field rt :world) :op (a operation p-id)
   :n (a (a operation p-ticket) x-id) :sequence (second (a operation p-id))})

(defn- operation-check! [rt operation]
  (let [frame (current-activation) ticket (a operation p-ticket)]
    (when-not (and frame (same-cell-world? rt (a frame 0))
                   (identical? operation (active-operation)) ticket
                   (identical? operation (a ticket x-operation))
                   (identical? ticket (find! (a (runtime-field rt :finalization) 0) (a ticket x-id)))
                   (= (second (a operation p-id)) (a ticket x-seq))
                   (not= :closed (a operation p-state))
                   (contains? (a operation p-frames) (a frame 11))
                   (pos? (long (a operation p-physical))))
      (throw (ex-info "Protected operation frame is no longer admitted" {:error :cleanup-only})))
    (when-not (operation-retired? operation)
      (let [run (a ticket x-run)]
        (when-not (and run (= (a operation p-parent) (run-id run))
                       (identical? run (current (a run r-node))))
          (throw (ex-info "Protected operation lost its exact parent generation" {:error :cleanup-only})))))))

(defn- clear-operation-registration! [rt operation registration]
  (if-let [consumer (a registration g-mailbox)]
    (if (= :entered (a consumer b-state)) (mailbox-return! rt consumer) (mailbox-detach! rt consumer))
    (dissoc! (a (a registration g-control) 3) (a registration g-id)))
  (note-cell-gc-blocker-change! rt (a registration g-allocation))
  (dissoc! (a operation p-registrations) (a registration g-id))
  (put registration g-resolve nil) (put registration g-reject nil)
  (put registration g-value nil) (put registration g-state :invalid))

(defn- queue-operation! [rt operation]
  (when (and (= :open (a operation p-state)) (zero? (long (a operation p-physical)))
             (not (a operation p-queued))
             (some #(= :ready (a % g-state)) (values (a operation p-registrations))))
    (put operation p-queued true)
    (push! (runtime-field rt :posts)
           (doto (slots 1) (put 0 #(invoke-operation-ready! rt operation))))))

(defn- operation-terminal! [rt operation value failed?]
  (locked rt
          (let [ticket (a operation p-ticket)]
            (when (and ticket (identical? operation (a ticket x-operation))
                       (= (second (a operation p-id)) (a ticket x-seq))
                       (= :open (a operation p-state)))
              (put operation p-state :terminal)
              (put operation p-terminal (if failed? :error :ok))
              (doseq [registration (vec (values (a operation p-registrations)))
                      :when (not= :claimed (a registration g-state))]
                (clear-operation-registration! rt operation registration))
              (put ticket x-phase :ready) (put ticket x-value value)
              (put ticket x-failed failed?) (put ticket x-delivered true)
              (boundary! rt (when (runtime-field rt :audit)
                              (assoc (operation-action rt operation :operation-terminal)
                                     :value (diagnostic-value value failed?) :variant (if failed? :error :ok))))
              (queue-cleanup! rt ticket)
              true))))

(defn- operation-terminal-callback [rt operation failed?]
  (let [weak #?(:clj (java.lang.ref.WeakReference. rt) :cljs (js/WeakRef. rt))
        id (a operation p-id)]
    (fn [value]
      (when-let [target #?(:clj (.get weak) :cljs (.deref weak))]
        (when-let [current (locked target
                                   (some-> (find! (a (runtime-field target :finalization) 0) (first id))
                                           (a x-operation)))]
          (when (= id (a current p-id))
            (operation-terminal! target current value failed?)
            (drain! target)))))))

(defn- return-operation-frame! [rt operation frame-id registration]
  (locked rt
          (when registration (clear-operation-registration! rt operation registration))
          (put operation p-physical (dec (long (a operation p-physical))))
          (put operation p-frames (disj (a operation p-frames) frame-id))
          (boundary! rt (when (runtime-field rt :audit)
                          (cond-> (assoc (operation-action rt operation :operation-return) :frame frame-id)
                            registration (assoc :reg (a registration g-id)))))
          (if (= :terminal (a operation p-state))
            (queue-cleanup! rt (a operation p-ticket))
            (queue-operation! rt operation))))

(defn- operation-frame [rt operation frame-id run]
  (doto (slots 12) (put 0 rt) (put 1 run) (put 2 -1)
        (put 10 operation) (put 11 frame-id)))

(defn- start-protected-operation! [rt start]
  (let [parent (current-activation)
        operation (locked rt
                          (let [ticket (deferred-ticket rt)]
                            (when-not (and ticket (= :waiting (a ticket x-phase))
                                           (nil? (a ticket x-operation)))
                              (throw (ex-info "Protected operation needs a fresh outer wait" {:error :not-waiting})))
                            (let [operation (doto (slots 11)
                                              (put p-id [(a ticket x-id) (a ticket x-seq)])
                                              (put p-ticket ticket) (put p-parent (nth (a ticket x-id) 2))
                                              (put p-state :open) (put p-registrations (dict))
                                              (put p-next 0) (put p-physical 1) (put p-frame-next 1)
                                              (put p-frames #{[[(a ticket x-id) (a ticket x-seq)] 1]}))]
                              (put ticket x-operation operation)
                              (boundary! rt (when (runtime-field rt :audit)
                                              (assoc (operation-action rt operation :operation-start)
                                                     :frame [(a operation p-id) 1])))
                              operation)))
        frame-id [(a operation p-id) 1]
        frame (operation-frame rt operation frame-id (a parent 1))]
    (try
      (with-activation frame
        (binding [cps/*in-trampoline* false]
          (cps/with-trampoline
            (start (operation-terminal-callback rt operation false)
                   (operation-terminal-callback rt operation true)))))
      (catch #?(:clj Throwable :cljs :default) error
        (when-not (operation-terminal! rt operation error true)
          (locked rt
                  (push! (runtime-field rt :posts) (doto (slots 1) (put 0 #(throw error)))))))
      (finally (return-operation-frame! rt operation frame-id nil)))))

(defn- operation-deliver! [rt registration value]
  (let [operation (a registration g-operation)]
    (when (and (= :open (a operation p-state)) (= :pending (a registration g-state))
               (identical? registration (find! (a operation p-registrations) (a registration g-id))))
      (dissoc! (a (a registration g-control) 3) (a registration g-id))
      (put registration g-state :ready) (put registration g-value value)
      (note-cell-gc-blocker-change! rt (a registration g-allocation))
      ;; Assignment and every readiness handoff share its deferred-assign
      ;; receipt; no intermediate refinement snapshot may consume half of it.
      (queue-operation! rt operation))))

(defn- invoke-operation-ready! [rt operation]
  (let [claim (locked rt
                      (put operation p-queued false)
                      (when (and (= :open (a operation p-state)) (zero? (long (a operation p-physical))))
                        (when-let [registration (first (sort-by #(last (a % g-id))
                                                                (filter #(= :ready (a % g-state))
                                                                        (values (a operation p-registrations)))))]
                          (when (a registration g-entered)
                            (throw (ex-info "Protected registration already entered" {:error :already-entered})))
                          (let [ordinal (put operation p-frame-next (inc (long (a operation p-frame-next))))
                                frame-id [(a operation p-id) ordinal]]
                            (put operation p-physical 1) (put operation p-frames #{frame-id})
                            (put registration g-state :claimed) (put registration g-entered true)
                            (when-let [consumer (a registration g-mailbox)] (mailbox-enter! rt consumer frame-id false false))
                            (boundary! rt (when (runtime-field rt :audit)
                                            (assoc (operation-action rt operation :operation-claim)
                                                   :reg (a registration g-id) :frame frame-id
                                                   :continuation (a registration g-id))))
                            [registration frame-id]))))]
    (when claim
      (let [[registration frame-id] claim
            frame (operation-frame rt operation frame-id nil)
            callback (a registration g-resolve) value (a registration g-value)]
        (try
          (public-slice! rt nil (a operation p-ticket) nil
                         (fn [] (with-activation frame
                                  (locked rt (operation-check! rt operation))
                                  (binding [cps/*in-trampoline* false]
                                    (cps/with-trampoline (cps/invoke-continuation callback value))))))
          (catch #?(:clj Throwable :cljs :default) error
            (when-not (operation-terminal! rt operation error true) (throw error)))
          (finally (return-operation-frame! rt operation frame-id registration)))))))

(defn- protect-deferred! [requested rt ref operation resolve reject]
  (let [resolve (cps-runtime/scope-continuation resolve)
        reject (cps-runtime/scope-continuation reject)
        registration (locked rt
                             (operation-check! rt operation)
                             (when-not (= :open (a operation p-state))
                               (throw (ex-info "Protected operation already settled" {:error :operation-settled})))
                             (let [ticket (a operation p-ticket)
                                   view (deferred-view! rt ref :protect) control (:control view)
                                   key (or (:key view) [(runtime-field rt :world) (owner-id (a (:node view) n-owner)) (:id ref)])
                                   profile (runtime-field rt :finalization)
                                   cell (or (:cell view) (find! (a profile 1) key)
                                            (doto (slots 5) (put 0 :deferred) (put 1 (a control 2))
                                                  (put 2 (members)) (put 3 (:id ref)) (put 4 control)))
                                   ordinal (put operation p-next (inc (long (a operation p-next))))
                                   registration (doto (slots 11)
                                                  (put g-entered false)
                                                  (put g-id [(a operation p-id) ordinal])
                                                  (put g-operation operation) (put g-allocation (:id ref))
                                                  (put g-control control) (put g-key key)
                                                  (put g-state (if (a control 1) :claimed :pending))
                                                  (put g-resolve resolve) (put g-reject reject)
                                                  (put g-value (a control 2)))]
                               (assoc! (a profile 1) key cell)
                               (add! (a cell 2) ticket) (assoc! (a ticket x-cells) key cell)
                               (assoc! (a operation p-registrations) (a registration g-id) registration)
                               (when-not (a control 1) (assoc! (a control 3) (a registration g-id) registration))
                               (note-cell-gc-blocker-change! rt (:id ref))
                               (boundary! rt (when (runtime-field rt :audit)
                                               (assoc (operation-action rt operation :operation-await)
                                                      :reg (a registration g-id) :e (:id ref) :allocation (:id ref)
                                                      :cell key :assigned? (boolean (a control 1))
                                                      :frame (a (current-activation) 11)
                                                      :continuation (a registration g-id)
                                                      :value (diagnostic-value (a control 2) false))))
                               registration))]
    (if (= :claimed (a registration g-state))
      (try
        (locked rt
                (when (a registration g-entered)
                  (throw (ex-info "Protected registration already entered" {:error :already-entered})))
                (put registration g-entered true)
                (boundary! rt (when (runtime-field rt :audit)
                                (assoc (operation-action rt operation :operation-claim)
                                       :reg (a registration g-id) :frame (a (current-activation) 11) :inline? true
                                       :continuation (a registration g-id)))))
        ;; Direct Deferred invocation owns its callback trampoline even when
        ;; the operation ignores its return value. The same physical frame
        ;; covers all registration-side Thunks.
        (binding [cps/*in-trampoline* false]
          (cps/with-trampoline (cps/invoke-continuation resolve (a registration g-value))))
        (finally
          (locked rt
                  (clear-operation-registration! rt operation registration)
                  (boundary! rt (when (runtime-field rt :audit)
                                  (assoc (operation-action rt operation :operation-return)
                                         :inline? true :reg (a registration g-id)
                                         :frame (a (current-activation) 11)))))))
      :org.replikativ.spindel.spin/incomplete)))

(defn- end-deferred-protection! [rt ticket]
  (when-let [operation (a ticket x-operation)]
    (doseq [registration (vec (values (a operation p-registrations)))]
      (if-let [consumer (a registration g-mailbox)]
        (if (= :entered (a consumer b-state)) (mailbox-return! rt consumer) (mailbox-detach! rt consumer))
        (dissoc! (a (a registration g-control) 3) (a registration g-id)))
      (put registration g-resolve nil) (put registration g-reject nil)
      (put registration g-value nil) (put registration g-state :invalid)
      (dissoc! (a operation p-registrations) (a registration g-id)))
    (put operation p-state :closed) (put operation p-ticket nil)
    (put ticket x-operation nil)))

(defn- assign-deferred! [rt event]
  ;; The dispatcher has claimed this exact envelope. Its source may have moved
  ;; into a retained cleanup cell since admission; the allocation stays fixed.
  (let [ref (a event 1) value (a event 3) aux (a event 6)]
    (when aux
      (put aux 2 (dec (long (a aux 2))))
      (note-cell-gc-blocker-change! rt (:id ref)))
    (when-let [view (deferred-view! rt ref :assign)]
      (let [control (:control view)]
        (when-not (a control 1)
          (put control 1 true) (put control 2 value)
          (when-let [node (:node view)]
            (put node n-complete true) (put node n-value value)
            (enqueue-source! rt node value))
          (when-let [cell (:cell view)] (put cell 1 value))
          (doseq [registration (sort-by #(last (a % g-id)) (vec (values (a control 3))))]
            (operation-deliver! rt registration value)))))
    (boundary! rt (when (runtime-field rt :audit)
                    (cond-> {:t :deferred-assign :w (runtime-field rt :world)
                             :e (:id ref) :allocation (:id ref) :seq (a event 2) :value value}
                      (a event 5) (assoc :cell (a event 5)))))))

(defn- await-public-deferred!
  ([requested target resolve reject] (await-public-deferred! requested target resolve reject nil))
  ([requested target resolve reject pending]
   (admit-world-switch! requested)
   (let [rt (canonical-runtime requested) ref (deferred-reference! rt target)
         frame (current-activation)
         resume-resolve (cps-runtime/scope-continuation resolve)
         resume-reject (cps-runtime/scope-continuation reject)]
     (when-not (and frame (same-cell-world? rt (a frame 0)))
       (throw (ex-info "Deferred await requires the selected activation" {:error :await-outside-activation})))
     (let [outcome (locked rt
                           (check-running! (a frame 1))
                           (let [view (deferred-view! rt ref :await) node (:node view)
                                 run (a frame 1) control (:control view)
                                 order (put frame 2 (inc (long (a frame 2))))
                                 ready? (boolean (a control 1)) value (a control 2)]
                             (when-not ready?
                               (ob! rt :await-once node run order resume-resolve resume-reject)
                               (put run r-status :parked)
                               (when (runtime-field rt :finalization) (put run r-cancel-cont resume-reject))
                               (note-cell-gc-blocker-change! rt (:id ref)))
                             (boundary! rt (when (runtime-field rt :audit)
                                             {:t :t05 :w (runtime-field rt :world) :r (run-id run)
                                              :kind :await-once :order order
                                              :debtor [:entity (runtime-field rt :world) (:id ref)]}))
                             [ready? value]))]
       (if (first outcome) (cps/invoke-continuation resolve (second outcome)) pending)))))

(defn invoke-public-deferred! [requested target resolve reject]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) ref (deferred-reference! rt target)
        frame (current-activation)
        operation (active-operation)]
    (cond
      operation (protect-deferred! requested rt ref operation resolve reject)
      (and frame (same-cell-world? rt (a frame 0)))
      (binding [cps/*in-trampoline* false]
        (await-public-deferred! requested target resolve reject :org.replikativ.spindel.spin/incomplete))
      :else
      (let [ready (locked rt
                          (let [view (deferred-view! rt ref :observe) control (:control view)]
                            (when-not (a control 1)
                              (let [ob (ob! rt :deref (:node view) nil 0 nil nil)]
                                (put ob o-success (fn [value]
                                                    (host-callback-scope requested
                                                                         #(binding [cps/*in-trampoline* false]
                                                                            (cps/invoke-continuation resolve %)) value)))
                                (put ob o-failure (fn [error]
                                                    (host-callback-scope requested
                                                                         #(binding [cps/*in-trampoline* false]
                                                                            (cps/invoke-continuation reject %)) error)))))
                            (boundary! rt (when (runtime-field rt :audit)
                                            (deferred-action rt ref view :deferred-observe)))
                            [(boolean (a control 1)) (a control 2)]))]
        (if (first ready)
          (host-callback-scope requested
                               #(binding [cps/*in-trampoline* false] (cps/invoke-continuation resolve %))
                               (second ready))
          :org.replikativ.spindel.spin/incomplete)))))

;; Mailbox state is engine-owned. The same control is shared by every retained
;; owner cohort; reservations remain cancellable until an exact physical claim.
(defn- mailbox-owner-anchor [rt view]
  (if-let [owner (some-> (:node view) (a n-owner))]
    (if (root-owner? owner) [(:id owner) (runtime-field rt :world)] (run-anchor rt owner))
    [(second (:key view)) (runtime-field rt :root) (runtime-field rt :world)]))

(defn- mailbox-callback-check! [rt receipt]
  (let [frame (current-activation)]
    (when-not (and frame (same-cell-world? rt (a frame 0))
                   (identical? receipt (active-mailbox-callback))
                   (identical? receipt (find! (a (runtime-field rt :finalization) 0) (a receipt x-id)))
                   (= :executing (a receipt x-phase)) (a receipt x-physical)
                   (let [consumer (a receipt 18)]
                     (and (#{:entered :rejection-entered} (a consumer b-state))
                          (= (a frame 11) (a consumer b-frame))
                          (identical? consumer (find! (a (a consumer b-control) m-physical) (a consumer b-frame))))))
      (throw (ex-info "Mailbox callback frame is no longer admitted" {:error :cleanup-only})))))

(defn- mailbox-reference! [rt target]
  (let [ref (rtp/mailbox-payload target)]
    (when-not (and (instance? MailboxRef ref) (identical? (:family ref) (runtime-field rt :family-id)))
      (throw (ex-info "Mailbox belongs to another engine or family" {:error :unknown-mailbox})))
    ref))

(defn- mailbox-view! [rt ref purpose]
  (let [id (:id ref) node (find! (runtime-field rt :nodes) id)
        aux (find! (a (runtime-field rt :managed-cells) 0) id)
        live? (and node aux (= :mailbox (a node n-kind)) (a node n-owner) (= id (a aux 0)))
        frame (current-activation) operation (active-operation) raw (active-mailbox-callback)
        ;; The live forwarding exception belongs to Mailbox synchronization.
        ;; Generic cells keep named-only raw callback rights even while live.
        cleanup? (if raw (boolean (a raw 20)) (cleanup-cell-access? rt))
        ticket (when-not (= :assign purpose)
                 (or raw (when operation (a operation p-ticket))
                     (when cleanup?
                       (or (a frame 8) (when-let [run (a frame 1)] (cleanup-adopt! rt run))))))
        retained (when (and (or ticket (= :assign purpose) (nil? frame))
                            (or cleanup? (not live?)))
                   (when-let [profile (runtime-field rt :finalization)]
                     (first (for [[key cell] (map-value (if ticket (a ticket x-cells) (a profile 1)))
                                  :when (and (= id (nth key 2)) (= :mailbox (a cell 0))
                                             (= id (a cell 3)) (pos? (count! (a cell 2))))]
                              {:key key :cell cell :control (a cell 4)}))))]
    (when-not (= :assign purpose)
      (when operation (operation-check! rt operation))
      (when raw (mailbox-callback-check! rt raw))
      (when-not (or (= :protect purpose) cleanup?
                    (and (= :post purpose) (nil? frame) retained (not live?)))
        (check-cell-caller! rt)))
    (when (and cleanup? (not= :protect purpose) (not retained))
      (throw (ex-info "Mailbox is outside the retained callback capability" {:error :missing-cleanup-cell :id id})))
    (when (and cleanup? (not operation) (not raw)
               (not= :assign purpose) (not= :claimed (some-> ticket (a x-phase))))
      (throw (ex-info "Mailbox cleanup frame is not claimed" {:error :cleanup-only})))
    (when (and retained (nil? frame) (not (#{:post :assign} purpose)))
      (throw (ex-info "A retired Mailbox permits host posting only" {:error :missing-mailbox :id id})))
    (when (and raw (or (a raw 20) (not live?)) (#{:take :observe} purpose))
      (throw (ex-info "Retired Mailbox callback cannot register ordinary work" {:error :cleanup-only})))
    (cond
      (and retained (or (not live?) (and cleanup? (not (and raw (not (a raw 20)))))))
      (assoc retained :node nil :aux nil)
      live? {:node node :aux aux :control (a node n-mailbox)}
      (= :assign purpose) nil
      :else (throw (ex-info "Released Mailbox allocation" {:error :missing-mailbox :id id})))))

(defn- mailbox-consumer-row [consumer]
  (let [ob (a consumer b-ob) registration (a consumer b-registration)]
    (cond-> {:kind (a consumer b-kind) :order (if registration (last (a registration g-id)) (a ob o-order))}
      ob (assoc :o [:o (a ob o-id)])
      (= :ordinary (a consumer b-kind)) (assoc :r (run-id (a consumer b-run)))
      registration (assoc :op (a (a registration g-operation) p-id) :reg (a registration g-id)))))

(defn- mailbox-metadata [control]
  {:messages (mapv (fn [[id value]] {:id id :value value}) (items (a control m-messages)))
   :consumers (mapv #(a % b-id) (items (a control m-consumers)))
   :pending (into {} (for [consumer (values (a control m-pending))]
                       [(a consumer b-id) (mailbox-consumer-row consumer)]))
   :reservations (into {} (for [consumer (values (a control m-reservations))
                                :let [[id value] (a consumer b-message)]]
                            [(a consumer b-id) (cond-> (assoc (mailbox-consumer-row consumer)
                                                              :message-id id :value value :state (a consumer b-state))
                                                 (a consumer b-frame) (assoc :frame (a consumer b-frame)))]))
   :protected (into {} (for [consumer (values (a control m-protected))
                             :let [registration (a consumer b-registration) operation (a registration g-operation)]]
                         [(a registration g-id) {:operation (a operation p-id) :sequence (second (a operation p-id))}]))
   :physical (into {} (for [[frame consumer] (map-value (a control m-physical))]
                        [frame {:consumer (a consumer b-id) :owner [(first (a consumer b-key)) (a consumer b-owner)]
                                :anchor (a consumer b-anchor) :kind (a consumer b-kind)}]))})

(defn create-public-mailbox! [requested _public-id]
  (let [rt (canonical-runtime requested)]
    (when-not (runtime-field rt :finalization)
      (throw (ex-info "Mailbox physical receipts require the native lifetime profile" {:error :profile-disabled})))
    (let [allocation (allocate-managed-source! requested nil {} :mailbox)]
      (->MailboxRef (:id allocation) (runtime-field rt :family-id) (:anchor allocation)))))

(defn- mailbox-action [rt consumer kind]
  {:t kind :w (runtime-field rt :world) :e (a consumer b-allocation) :allocation (a consumer b-allocation)
   :consumer (a consumer b-id)})

(defn- refresh-mailbox-owner! [rt consumer owner]
  ;; Pending consumers have no physical owner witness yet. Prefix adoption
  ;; may move the allocation before their callback is claimed. Once seated,
  ;; its receipt keeps the exact owner/anchor until actual physical return.
  (when (and owner (nil? (a consumer b-receipt)) (not= :operation (a consumer b-kind)))
    (let [id (owner-id owner)]
      (put consumer b-owner id)
      (put consumer b-key [(runtime-field rt :world) id (a consumer b-allocation)])
      (put consumer b-anchor (if (root-owner? owner) [id (runtime-field rt :world)] (run-anchor rt owner))))))

(defn- retain-mailbox-frame! [rt consumer frame]
  (when-not (a consumer b-receipt)
    (refresh-mailbox-owner! rt consumer (some-> (a consumer b-node) (a n-owner)))
    (let [profile (runtime-field rt :finalization) key (a consumer b-key)
          control (a consumer b-control)
          cell (or (find! (a profile 1) key)
                   (doto (slots 5) (put 0 :mailbox) (put 2 (members))
                         (put 3 (a consumer b-allocation)) (put 4 control)))
          receipt (doto (slots 21)
                    (put x-id [:mailbox-callback (runtime-field rt :world) (a consumer b-owner) (a consumer b-id)])
                    (put x-kind :mailbox-callback) (put x-anchor (a consumer b-anchor))
                    (put x-phase (if frame :executing :queued)) (put x-physical (boolean frame)) (put x-cells (id-dict))
                    (put 18 consumer) (put 19 (a consumer b-owner))
                    (put 20 (nil? (some-> (a consumer b-node) (a n-owner)))))]
      (assoc! (a profile 1) key cell)
      (add! (a cell 2) receipt) (assoc! (a receipt x-cells) key cell)
      (assoc! (a profile 0) (a receipt x-id) receipt)
      (put consumer b-frame frame) (put consumer b-receipt receipt)
      (when frame (assoc! (a control m-physical) frame consumer)))))

(defn- queue-mailbox-envelope! [rt ref view message repost?]
  (let [counters (runtime-field rt :counters)
        sequence (put counters 2 (inc (max (long (a counters 1)) (long (a counters 2)))))
        message (or message [[(:id ref) sequence] nil])
        aux (:aux view)
        event (doto (slots 9) (put 0 rt) (put 1 ref) (put 2 sequence) (put 3 message)
                    (put 4 :mailbox-post) (put 5 (:key view)) (put 6 aux) (put 7 repost?))]
    (when aux (put aux 2 (inc (long (a aux 2)))))
    (push! (runtime-field rt :events) event)
    event))

(defn post-public-mailbox! [requested target value]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) ref (mailbox-reference! rt target)]
    (locked rt
            (let [view (mailbox-view! rt ref :post)
                  event (queue-mailbox-envelope! rt ref view nil false)
                  message [[(:id ref) (a event 2)] value]]
              (put event 3 message)
              (boundary! rt (when (runtime-field rt :audit)
                              (cond-> {:t :mailbox-post-request :w (runtime-field rt :world) :e (:id ref)
                                       :allocation (:id ref) :value value :message-id (first message)}
                                (:key view) (assoc :cell (:key view))
                                (when-let [frame (current-activation)] (same-cell-world? rt (a frame 0)))
                                (assoc :th :engine))))))
    (drain! rt))
  nil)

(defn- mailbox-unlink-pending! [control consumer]
  (dissoc! (a control m-pending) (a consumer b-id))
  (let [pending (a control m-consumers)]
    (if (identical? consumer (queue-front pending))
      (pop! pending)
      #?(:clj (.remove ^java.util.ArrayDeque pending consumer)
         :cljs (.remove pending consumer))))
  (when-let [registration (a consumer b-registration)]
    (dissoc! (a control m-protected) (a registration g-id))))

(defn- mailbox-detach! [rt consumer]
  (let [state (a consumer b-state) control (a consumer b-control)]
    (when (#{:pending :reserved} state)
      (mailbox-unlink-pending! control consumer)
      (dissoc! (a control m-reservations) (a consumer b-id))
      (when (and (= :reserved state) (a consumer b-message))
        (let [ref (->MailboxRef (a consumer b-allocation) (runtime-field rt :family-id) nil)
              view (mailbox-view! rt ref :assign)]
          (when view (queue-mailbox-envelope! rt ref view (a consumer b-message) true))))
      (put consumer b-state :detached) (put consumer b-message nil)
      (put consumer b-resolve nil) (put consumer b-reject nil)
      (note-cell-gc-blocker-change! rt (a consumer b-allocation)))))

(defn- mailbox-enter! [rt consumer frame inline? audit?]
  (let [state (a consumer b-state) ob (a consumer b-ob) run (a consumer b-run)
        ;; Buffered takes already seated their physical receipt. Keep that
        ;; exact key: the CLJS physical map compares frame keys by identity.
        frame (or (a consumer b-frame) frame)
        operation (some-> (a consumer b-registration) (a g-operation))]
    (when-not (#{:reserved :claimed} state)
      (throw (ex-info "Mailbox reservation is not enterable" {:error :not-mailbox-reservation})))
    (when (and run (not (and inline? (= :claimed state))))
      (when-not (and (a ob o-live) (identical? run (current (a run r-node)))
                     (= (a run r-gen) (a ob o-creditor-generation)) (not= :unwinding (a run r-status)))
        (throw (ex-info "Mailbox consumer is no longer current" {:error :cancelled}))))
    (put consumer b-state :entered) (put consumer b-frame frame)
    (when-not operation (retain-mailbox-frame! rt consumer frame))
    (when ob
      (put ob o-value (second (a consumer b-message))) (put ob o-delivery-error false)
      (put ob o-slot :consumed) (end-ob! rt ob))
    (note-cell-gc-blocker-change! rt (a consumer b-allocation))
    (when audit?
      (boundary! rt (when (runtime-field rt :audit)
                      (cond-> (assoc (mailbox-action rt consumer :mailbox-claim)
                                     :message-id (first (a consumer b-message)) :frame frame :inline? inline?)
                        run (assoc :r (run-id run) :th :engine)))))))

(defn- mailbox-return! [rt consumer]
  (when (#{:entered :rejection-entered} (a consumer b-state))
    (let [control (a consumer b-control) receipt (a consumer b-receipt) frame (a consumer b-frame)]
      (dissoc! (a control m-reservations) (a consumer b-id))
      (dissoc! (a control m-physical) frame)
      (when receipt
        (release-ticket-cells! rt receipt)
        (dissoc! (a (runtime-field rt :finalization) 0) (a receipt x-id))
        (put receipt x-physical false) (put receipt 18 nil))
      (put consumer b-state :returned) (put consumer b-message nil) (put consumer b-error nil) (put consumer b-error-receipt nil)
      (put consumer b-resolve nil) (put consumer b-reject nil)
      (put consumer b-context nil) (put consumer b-node nil)
      (when (not= :operation (a consumer b-kind))
        (boundary! rt (when (runtime-field rt :audit)
                        (assoc (mailbox-action rt consumer :mailbox-return) :frame frame)))))))

(defn- run-mailbox-host! [rt consumer]
  (let [entered? (locked rt
                         (when (= :reserved (a consumer b-state))
                           (mailbox-enter! rt consumer [:mailbox-frame (a consumer b-id)] false true)
                           true))]
    (when entered?
      (let [frame (doto (slots 14) (put 0 rt) (put 2 -1)
                        (put 11 (a consumer b-frame)) (put 12 (a consumer b-receipt)) (put 13 consumer))
            callback (a consumer b-resolve) value (second (a consumer b-message))
            context (a consumer b-context)]
        (try
          (host-callback-scope context
                               (fn [value]
                                 (with-activation frame
                                   (binding [cps/*in-trampoline* false]
                                     (cps/with-trampoline (cps/invoke-continuation callback value))))) value)
          (finally (locked rt (mailbox-return! rt consumer))))))))

(defn- reserve-mailbox! [rt consumer message state]
  (let [control (a consumer b-control)]
    (mailbox-unlink-pending! control consumer)
    (put consumer b-state state) (put consumer b-message message)
    (assoc! (a control m-reservations) (a consumer b-id) consumer)
    (if-let [registration (a consumer b-registration)]
      (let [operation (a registration g-operation)]
        (put registration g-value (second message))
        (put registration g-state (if (= :claimed state) :claimed :ready))
        (queue-operation! rt operation))
      (when (= :reserved state)
        (if-let [run (a consumer b-run)]
          (do (put run r-status :running) (schedule! rt (a run r-node) (a consumer b-ob)))
          (push! (runtime-field rt :posts) (doto (slots 1) (put 0 #(run-mailbox-host! rt consumer)))))))))

(defn- process-mailbox-post! [rt event]
  (let [ref (a event 1) aux (a event 6)]
    (when aux (put aux 2 (dec (long (a aux 2)))))
    (when-let [view (mailbox-view! rt ref :assign)]
      (let [control (:control view)
            consumer (loop []
                       (when-let [consumer (queue-front (a control m-consumers))]
                         (let [ob (a consumer b-ob) run (a consumer b-run)
                               registration (a consumer b-registration)
                               admissible? (and (= :pending (a consumer b-state))
                                                (if registration
                                                  (let [operation (a registration g-operation)]
                                                    (and (= :open (a operation p-state))
                                                         (identical? registration (find! (a operation p-registrations) (a registration g-id)))))
                                                  (and (a ob o-live)
                                                       (or (nil? run)
                                                           (and (identical? run (current (a run r-node)))
                                                                (not= :unwinding (a run r-status)))))))]
                           (if admissible? consumer
                               (do (mailbox-detach! rt consumer)
                                   (when (identical? consumer (queue-front (a control m-consumers)))
                                     (mailbox-unlink-pending! control consumer))
                                   (when (and ob (a ob o-live)) (end-ob! rt ob))
                                   (recur))))))]
        (if consumer (reserve-mailbox! rt consumer (a event 3) :reserved)
            (push! (a control m-messages) (a event 3)))))
    (note-cell-gc-blocker-change! rt (:id ref))
    (boundary! rt (when (runtime-field rt :audit)
                    (cond-> {:t :mailbox-post :w (runtime-field rt :world) :e (:id ref) :allocation (:id ref)
                             :seq (a event 2) :message-id (first (a event 3)) :value (second (a event 3))}
                      (a event 5) (assoc :cell (a event 5)) (a event 7) (assoc :repost? true))))))

(defn- new-mailbox-consumer! [rt ref view kind ob registration resolve reject]
  (let [control (:control view) id (if registration [:operation (a registration g-id)]
                                       [(if (= :ordinary kind) :obligation :host) [:o (a ob o-id)]])
        key (or (:key view) [(runtime-field rt :world) (owner-id (a (:node view) n-owner)) (:id ref)])
        consumer (doto (slots 20) (put b-id id) (put b-kind kind) (put b-ob ob)
                       (put b-registration registration) (put b-state :pending)
                       (put b-resolve resolve) (put b-reject reject)
                       (put b-anchor (mailbox-owner-anchor rt view)) (put b-owner (second key))
                       (put b-control control) (put b-allocation (:id ref)) (put b-key key)
                       (put b-node (:node view)) (put b-context ec/*execution-context*) (put b-run (when ob (a ob o-run))))]
    (when ob (put ob o-mailbox consumer))
    consumer))

(defn- mailbox-add-take! [rt consumer]
  (let [control (a consumer b-control)]
    (if (queued? (a control m-messages))
      (let [message (pop! (a control m-messages))]
        (reserve-mailbox! rt consumer message :claimed)
        (if (= :operation (a consumer b-kind))
          (put consumer b-frame (a (current-activation) 11))
          (retain-mailbox-frame! rt consumer [:mailbox-frame (a consumer b-id)]))
        true)
      (do
        (push! (a control m-consumers) consumer)
        (assoc! (a control m-pending) (a consumer b-id) consumer)
        (when-let [registration (a consumer b-registration)]
          (assoc! (a control m-protected) (a registration g-id) consumer))
        false))))

(defn- mailbox-cancelled-id? [rt id]
  (when id (when-let [node (find! (runtime-field rt :nodes) id)]
             (or (a node n-cancelled) (= :unwinding (some-> (current node) (a r-status)))))))

(defn take-public-mailbox-now! [requested target consumer-id]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) ref (mailbox-reference! rt target)]
    (locked rt
            (let [view (mailbox-view! rt ref :read) control (:control view)
                  available? (and (not (mailbox-cancelled-id? rt consumer-id))
                                  (queued? (a control m-messages)) (not (queued? (a control m-consumers))))
                  message (when available? (pop! (a control m-messages)))]
              (boundary! rt (when (runtime-field rt :audit)
                              (cond-> {:t :mailbox-take-now :w (runtime-field rt :world) :e (:id ref)
                                       :allocation (:id ref) :consumer-id consumer-id :available? (boolean available?)}
                                message (assoc :message-id (first message)) (:key view) (assoc :cell (:key view))
                                (when-let [frame (current-activation)] (same-cell-world? rt (a frame 0)))
                                (assoc :th :engine))))
              {:available? (boolean available?) :value (second message)}))))

(defn- protect-mailbox! [requested rt ref operation resolve reject direct?]
  (let [resolve (cps-runtime/scope-continuation resolve) reject (cps-runtime/scope-continuation reject)
        consumer (locked rt
                         (operation-check! rt operation)
                         (when-not (= :open (a operation p-state)) (throw (ex-info "Operation settled" {:error :operation-settled})))
                         (let [view (mailbox-view! rt ref :protect) ticket (a operation p-ticket)
                               key (or (:key view) [(runtime-field rt :world) (owner-id (a (:node view) n-owner)) (:id ref)])
                               profile (runtime-field rt :finalization)
                               cell (or (:cell view) (find! (a profile 1) key)
                                        (doto (slots 5) (put 0 :mailbox) (put 2 (members))
                                              (put 3 (:id ref)) (put 4 (:control view))))
                               ordinal (put operation p-next (inc (long (a operation p-next))))
                               registration (doto (slots 11) (put g-id [(a operation p-id) ordinal])
                                                  (put g-operation operation) (put g-allocation (:id ref))
                                                  (put g-control (:control view)) (put g-key key) (put g-state :pending)
                                                  (put g-resolve resolve) (put g-reject reject) (put g-entered false))
                               consumer (new-mailbox-consumer! rt ref view :operation nil registration resolve reject)]
                           (put registration g-mailbox consumer)
                           (assoc! (a profile 1) key cell) (add! (a cell 2) ticket) (assoc! (a ticket x-cells) key cell)
                           (assoc! (a operation p-registrations) (a registration g-id) registration)
                           (let [available? (mailbox-add-take! rt consumer)]
                             (boundary! rt (when (runtime-field rt :audit)
                                             (assoc (operation-action rt operation :operation-await)
                                                    :reg (a registration g-id) :frame (a (current-activation) 11)
                                                    :continuation (a registration g-id) :e (:id ref) :allocation (:id ref)
                                                    :cell key :available? available?)))
                             consumer)))]
    (if (= :claimed (a consumer b-state))
      (let [registration (a consumer b-registration)]
        (try
          (locked rt
                  (put registration g-entered true)
                  (mailbox-enter! rt consumer (a (current-activation) 11) true false)
                  (boundary! rt (when (runtime-field rt :audit)
                                  (assoc (operation-action rt operation :operation-claim)
                                         :reg (a registration g-id) :frame (a (current-activation) 11)
                                         :continuation (a registration g-id) :inline? true))))
          (if direct?
            (binding [cps/*in-trampoline* false]
              (cps/with-trampoline (cps/invoke-continuation resolve (a registration g-value))))
            (cps/invoke-continuation resolve (a registration g-value)))
          (finally
            (locked rt
                    (clear-operation-registration! rt operation registration)
                    (boundary! rt (when (runtime-field rt :audit)
                                    (assoc (operation-action rt operation :operation-return)
                                           :reg (a registration g-id) :frame (a (current-activation) 11) :inline? true)))))))
      :org.replikativ.spindel.spin/incomplete)))

(defn await-public-mailbox! [requested target resolve reject direct?]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) ref (mailbox-reference! rt target) frame (current-activation)]
    (if-let [operation (active-operation)]
      (protect-mailbox! requested rt ref operation resolve reject direct?)
      (let [run (when (and frame (same-cell-world? rt (a frame 0))) (a frame 1))
            scoped-resolve (cps-runtime/scope-continuation resolve) scoped-reject (cps-runtime/scope-continuation reject)
            consumer (locked rt
                             (when run (check-running! run))
                             (let [view (mailbox-view! rt ref (if run :take :observe))
                                   kind (if run :ordinary :host)
                                   order (if run (put frame 2 (inc (long (a frame 2)))) 0)
                                   ob (ob! rt (if run :await-once :deref) (:node view) run order scoped-resolve scoped-reject)
                                   consumer (new-mailbox-consumer! rt ref view kind ob nil scoped-resolve scoped-reject)
                                   _ (put consumer b-context requested)
                                   available? (mailbox-add-take! rt consumer)]
                               (when-not available?
                                 (when run (put run r-status :parked)
                                       (when (runtime-field rt :finalization) (put run r-cancel-cont scoped-reject))))
                               (put ob o-failure (fn [error]
                                                   (host-callback-scope requested
                                                                        #(binding [cps/*in-trampoline* false]
                                                                           (cps/invoke-continuation scoped-reject %)) error)))
                               (boundary! rt (when (runtime-field rt :audit)
                                               (cond-> (assoc (mailbox-action rt consumer :mailbox-take)
                                                              :kind kind :o [:o (a ob o-id)] :order order :available? available?)
                                                 run (assoc :r (run-id run) :th :engine)
                                                 (:key view) (assoc :cell (:key view)))))
                               consumer))]
        (if (= :claimed (a consumer b-state))
          (try
            (locked rt (mailbox-enter! rt consumer [:mailbox-frame (a consumer b-id)] true true))
            (let [value (second (a consumer b-message))
                  invoke (fn [value]
                           (if direct?
                             (binding [cps/*in-trampoline* false]
                               (cps/with-trampoline (cps/invoke-continuation resolve value)))
                             (cps/invoke-continuation resolve value)))]
              (if run
                (invoke value)
                (let [raw-frame (doto (slots 14) (put 0 rt) (put 2 -1)
                                      (put 11 (a consumer b-frame)) (put 12 (a consumer b-receipt)) (put 13 consumer))]
                  (host-callback-scope requested #(with-activation raw-frame (invoke %)) value))))
            (finally (locked rt (mailbox-return! rt consumer))))
          :org.replikativ.spindel.spin/incomplete)))))

(defn invoke-public-mailbox! [requested target resolve reject]
  (await-public-mailbox! requested target resolve reject true))

(defn- queue-mailbox-rejection! [rt consumer error cause]
  ;; Logical retirement owns this callback before removing its obligation.
  ;; It retains only the named allocation while queued; no physical frame is
  ;; invented until the actual error continuation is entered.
  (let [reject (a consumer b-reject)]
    (retain-mailbox-frame! rt consumer nil)
    (mailbox-detach! rt consumer)
    (put consumer b-state :rejection-queued) (put consumer b-error error)
    (put (a consumer b-receipt) 20 true)
    (put consumer b-error-receipt (if (= :cancelled cause)
                                    ::rtp/cancelled (diagnostic-value error true)))
    (put consumer b-reject reject) (put consumer b-node nil)
    (push! (runtime-field rt :posts)
           (doto (slots 1) (put 0 #(invoke-mailbox-rejection! rt consumer))))))

(defn- invoke-mailbox-rejection! [rt consumer]
  (let [entered? (locked rt
                         (let [receipt (a consumer b-receipt)]
                           (when (and (= :rejection-queued (a consumer b-state))
                                      (identical? receipt (find! (a (runtime-field rt :finalization) 0) (a receipt x-id))))
                             (let [frame [:mailbox-frame (a consumer b-id)]]
                               (put consumer b-state :rejection-entered) (put consumer b-frame frame)
                               (put receipt x-phase :executing) (put receipt x-physical true)
                               (assoc! (a (a consumer b-control) m-physical) frame consumer)
                               (boundary! rt (when (runtime-field rt :audit)
                                               (assoc (mailbox-action rt consumer :mailbox-claim)
                                                      :variant :error :callback (a receipt x-id) :frame frame)))
                               true))))]
    (when entered?
      (let [frame (doto (slots 14) (put 0 rt) (put 2 -1) (put 11 (a consumer b-frame))
                        (put 12 (a consumer b-receipt)) (put 13 consumer))
            reject (a consumer b-reject) error (a consumer b-error)]
        (try
          (host-callback-scope (a consumer b-context)
                               (fn [error]
                                 (with-activation frame
                                   (binding [cps/*in-trampoline* false]
                                     (cps/with-trampoline (cps/invoke-continuation reject error))))) error)
          (finally (locked rt (mailbox-return! rt consumer))))))))

(defn invoke-public-mailbox-next! [requested target resolve reject]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) frame (current-activation)
        next-resolve (fn [value] (cps/invoke-continuation resolve [value target]))]
    (cond
      ;; Operation reads acquire the target capability and enter their exact
      ;; supplied continuation on the existing frame, including buffered data.
      (active-operation)
      (await-public-mailbox! requested target next-resolve reject false)

      (and frame (same-cell-world? rt (a frame 0)))
      (let [run (a frame 1)
            ready (take-public-mailbox-now! requested target
                                            (when run (a (a run r-node) n-id)))]
        (if (:available? ready)
          (do
            (when run (put frame 2 (inc (long (a frame 2)))))
            ;; The frame's existing trampoline owns this return. In particular,
            ;; an async reduction must not nest a new pump for every item.
            (cps/invoke-continuation resolve [(:value ready) target]))
          (await-public-mailbox! requested target next-resolve reject false)))

      ;; The first raw call owns a real host take and callback physical frame.
      ;; That frame pumps the whole CPS callback, including any returned Thunks;
      ;; later buffered next calls can reuse it through the branch above.
      :else (await-public-mailbox! requested target next-resolve reject true))))

;; Explicit release owns unfinished cleanup. Ordinary pending worlds never
;; enter this registry, and joined receipts retain only their revoked facade.
(defn- release-id [rt] [:world-release (runtime-field rt :world)])

(defn- release-observer-row [rt]
  (let [state (runtime-field rt :lifecycle)]
    (cond-> {:id (release-id rt) :reason (diagnostic-value (a state 1) true)
             :phase (if (= :joined (a state 0)) :joined :releasing)
             :next-observer (a state 4)
             :observers (into {} (for [[id observer] (map-value (a state 5))]
                                   [id {:state (a observer 0)}]))}
      (= :joined (a state 0)) (assoc :result nil))))

(defn- release-view [rt live]
  (let [world (runtime-field rt :world)
        outside (mapv (fn [event] {:w world :event event})
                      (filter #(or (:deferred-assignment %) (:mailbox-post %)) (:queue live)))]
    (merge (select-keys live [:global :threads :native :cleanup-cells :gc :handles :principals :cleanup-targets])
           {:id world :lineage (runtime-field rt :lineage) :status :released
            :release (when (a (runtime-field rt :lifecycle) 3) (release-observer-row rt)) :outside outside})))

(defn- release-notify! [rt id]
  (let [callback (locked rt
                         (let [state (runtime-field rt :lifecycle)
                               observer (find! (a state 5) id)]
                           (when (and observer (= :ready (a observer 0)))
                             (dissoc! (a state 5) id)
                             (let [callback [(a observer 1) (a observer 3)]]
                               (put observer 1 nil) (put observer 2 nil) (put observer 3 nil)
                               (boundary! rt (when (runtime-field rt :audit)
                                               {:t :release-notify :w (runtime-field rt :world)
                                                :release (release-id rt) :observer id}))
                               callback))))]
    (when callback
      (host-callback-scope (second callback)
                           #(binding [cps/*in-trampoline* false]
                              (cps/with-trampoline (cps/invoke-continuation (first callback) %))) nil))))

(defn- queue-release-observer! [rt id observer]
  (when (= :waiting (a observer 0))
    (put observer 0 :ready)
    (push! (runtime-field rt :posts) (doto (slots 1) (put 0 #(release-notify! rt id))))))

(defn- revoke-release-arena! [rt]
  (let [old @(runtime-field rt :arena-cell)
        original-family (:family old)
        retired-global (global-view rt)
        _ (custody-release-data! rt)
        tombstone {:custody-tombstone true :world (runtime-field rt :world) :lineage (:lineage old)
                   :root (runtime-field rt :owner-root) :release-data (a (:lifecycle old) 6)
                   :generation-clock (into {} (for [[id n] (when-let [clock (a (:counters old) 3)] (map-value clock))]
                                                [[(runtime-field rt :world) id] n]))}
        family (id-dict) counters (doto (slots 12)
                                    (put 0 (queue)) (put 1 (a (:counters old) 1)) (put 2 (a (:counters old) 2))
                                    (put 3 (a (:counters old) 3)) (put 4 (slots 32)) (put 5 (slots 14))
                                    (put 6 (members)) (put 7 (id-dict)) (put 8 (members))
                                    (put 9 (when (:audit old) (queue)))
                                    (put 11 {:custody-retired retired-global}))
        empty-profile (when (:finalization old)
                        (doto (slots 5) (put 0 (id-dict)) (put 1 (id-dict)) (put 2 (queue)) (put 3 (id-dict))))
        state (map->ArenaState
               {:nodes (id-dict) :deliveries (dict) :events (queue) :hosts (queue) :posts (queue)
                :work (queue) :ready #?(:clj (java.util.PriorityQueue. 11 (reify java.util.Comparator
                                                                            (compare [_ x y] (compare (long (a x n-rank)) (long (a y n-rank))))))
                                        :cljs (array))
                :draining (atom false) :counters counters :audit (:audit old) :tokens (:tokens old)
                :serial (doto (slots 2) (put 0 (a (:serial old) 0)) (put 1 (a (:serial old) 1)))
                :thread (doto (slots 5)
                          ;; Keep only value-only thread history, never an old
                          ;; physical run or cleanup ticket after joining.
                          (put 1 (a (:thread old) 1)) (put 2 (a (:thread old) 2))
                          (put 3 (a (:thread old) 3)))
                :family family :parent nil :tickets (id-dict) :lineage (:lineage old) :gc (queue)
                :operations (dict) :execution-scopes (volatile! nil)
                :home (->RuntimeFamily (runtime-field rt :gate) family
                                       #?(:clj (java.util.WeakHashMap.) :cljs (js/WeakMap.))
                                       (doto (slots 5) (put 0 (queue)) (put 1 (id-dict)) (put 2 false) (put 3 0) (put 4 0)))
                :liveness (doto (slots 6) (put 0 (queue)) (put 1 (members)) (put 2 (members))
                                (put 3 (members)) (put 4 (queue)) (put 5 (dict)))
                :extension-state (atom {:values {} :shadowed #{} :map-groups #{}})
                :finalization empty-profile
                :managed-cells (doto (slots 3) (put 0 (id-dict)) (put 1 (id-dict)) (put 2 false))
                :trace-address (slots 1)
                :timers (doto (slots 3) (put 0 (id-dict)) (put 1 timer-transport/default-transport) (put 2 (queue)))
                :lifecycle (:lifecycle old)})]
    (assoc! original-family (runtime-field rt :world) tombstone)
    (vreset! (runtime-field rt :arena-cell) state)
    (assoc! family (runtime-field rt :world) (release-context-backend rt))))

(defn- stale-release-packet? [rt event]
  (let [size (alength ^objects event)
        kind (cond (and (= 7 size) (= :deferred-assignment (a event 4))) :deferred
                   (and (= 9 size) (= :mailbox-post (a event 4))) :mailbox)]
    (when (and kind (same-cell-world? rt (a event 0)))
      (let [id (:id (a event 1))
            node (find! (runtime-field rt :nodes) id)
            aux (find! (a (runtime-field rt :managed-cells) 0) id)
            live? (and node aux (= kind (a node n-kind)) (a node n-owner) (= id (a aux 0)))
            held? (when-let [profile (runtime-field rt :finalization)]
                    (some (fn [[key cell]]
                            (and (= (runtime-field rt :world) (nth key 0)) (= id (nth key 2))
                                 (= kind (a cell 0)) (= id (a cell 3)) (pos? (count! (a cell 2)))))
                          (map-value (a profile 1))))]
        (not (or live? held?))))))

(defn- prune-release-packets! [rt]
  ;; Only admitted producer attempts whose exact allocation has lost every
  ;; owner/cohort can disappear. Notifications and other worlds retain order.
  (let [events (runtime-field rt :events) copied (copy-items events)]
    #?(:clj (.clear ^java.util.ArrayDeque events) :cljs (.clear events))
    (dotimes [i (alength ^objects copied)]
      (let [event (a copied i)]
        (put copied i nil)
        (when-not (stale-release-packet? rt event) (push! events event))))))

(defn- refresh-release! [rt]
  (let [state (runtime-field rt :lifecycle)]
    (when (and (= :releasing (a state 0))
               (not (custody-debts? rt))
               (not-any? #(a % r-physical) (items (a (runtime-field rt :counters) 6)))
               (empty-dict? (a (runtime-field rt :timers) 0))
               (or (nil? (runtime-field rt :finalization))
                   (empty-dict? (a (runtime-field rt :finalization) 0))))
      (prune-release-packets! rt)
      (put state 0 :joined)
      ;; Publish onto the admitted shared FIFO before detaching the facade.
      ;; Only the queued closure retains this minimal observer backend; the
      ;; completed receipt never retains the old queues or sibling arenas.
      (doseq [[id observer] (map-value (a state 5))] (queue-release-observer! rt id observer))
      (revoke-release-arena! rt)
      (swap! pending-releases dissoc (runtime-field rt :owner-root)))))

(defn- release-authenticate! [rt receipt]
  (when-not (and (instance? NativeReleaseReceipt receipt)
                 (identical? receipt (a (runtime-field rt :lifecycle) 2)))
    (throw (ex-info "Release receipt belongs to another lifetime" {:error :foreign-release-receipt}))))

(defn- release-wait-admission! [rt]
  (when-let [frame (current-activation)]
    (when (contains? (locked rt (custody-reachable-roots rt false))
                     (runtime-field (a frame 0) :owner-root))
      (throw (ex-info "Release cannot await a physical frame in its cleanup closure" {:error :self-release-join})))
    (when (or (active-operation) (active-mailbox-callback))
      (throw (ex-info "Protected resource lifecycle waits require typed integration"
                      {:error :unsupported-operation :operation :protected-release-wait})))
    (locked (a frame 0) (check-running! (a frame 1)))))

(defn observe-world-release! [requested receipt resolve reject]
  (let [rt (release-context-backend (canonical-runtime requested))]
    (release-wait-admission! rt)
    (let [resolve (cps-runtime/scope-continuation resolve)
          reject (cps-runtime/scope-continuation reject)
          id (locked rt
                     (release-authenticate! rt receipt)
                     (let [state (runtime-field rt :lifecycle)
                           ordinal (put state 4 (inc (long (a state 4))))
                           id [(release-id rt) ordinal]
                           observer (doto (slots 4) (put 0 :waiting) (put 1 resolve) (put 2 reject)
                                          (put 3 ec/*execution-context*))]
                       (assoc! (a state 5) id observer)
                       (when (= :joined (a state 0)) (queue-release-observer! rt id observer))
                       (boundary! rt (when (runtime-field rt :audit)
                                       {:t :release-observe :w (runtime-field rt :world)
                                        :release (release-id rt) :observer id}))
                       id))]
      (drain! rt)
      (fn []
        (locked rt
                (release-authenticate! rt receipt)
                (when-let [observer (find! (a (runtime-field rt :lifecycle) 5) id)]
                  (put observer 1 nil) (put observer 2 nil) (put observer 3 nil)
                  (dissoc! (a (runtime-field rt :lifecycle) 5) id))
                (boundary! rt (when (runtime-field rt :audit)
                                {:t :release-detach :w (runtime-field rt :world)
                                 :release (release-id rt) :observer id})))))))

(defn- retain-world-cleanup! [rt reason]
  (when-let [profile (runtime-field rt :finalization)]
    (doseq [run (vec (items (a (runtime-field rt :counters) 6)))]
      (retain-cleanup! rt run {:reason reason :node (a run r-node)}))
    (let [participants (filter #(= :cps-exit (a % x-kind)) (values (a profile 0)))]
      (doseq [node (values (runtime-field rt :nodes))
              :when (and (a node n-owner) (#{:atom :signal :deferred :mailbox} (a node n-kind)))]
        (let [key [(runtime-field rt :world) (owner-id (a node n-owner)) (a node n-id)]
              cell (or (find! (a profile 1) key)
                       (doto (slots 5) (put 0 (a node n-kind)) (put 1 (a node n-value))
                             (put 2 (members)) (put 3 (source-allocation rt (a node n-id)))
                             (put 4 (case (a node n-kind) :deferred (a node n-deferred) :mailbox (a node n-mailbox) nil))))]
          (when (seq participants)
            (assoc! (a profile 1) key cell)
            (doseq [ticket participants]
              (add! (a cell 2) ticket) (assoc! (a ticket x-cells) key cell))))))
    (doseq [ticket (values (a profile 0)) :when (= :mailbox-callback (a ticket x-kind))]
      (put ticket 20 true))))

(def ^:private ^:dynamic *custody-terminal-release* false)

(defn request-world-release! [requested reason]
  (when-not *custody-terminal-release*
    (when (or (active-operation) (active-mailbox-callback))
      (throw (ex-info "Resource callbacks cannot release worlds" {:error :cleanup-only})))
    (admit-world-switch! requested))
  (let [rt (canonical-runtime requested) dispatch @(runtime-field rt :arena-cell)
        completion (locked rt
                           (let [state (runtime-field rt :lifecycle)]
                             (if (not= :live (a state 0))
                               (or (a state 3)
                                   (when-not *custody-terminal-release*
                                     (let [receipt (NativeReleaseReceipt. (runtime-field rt :owner-root) #?(:clj (Object.) :cljs (js-obj)))
                                           completion (lifecycle/completion (release-context-backend rt) receipt)]
                                       (put state 2 receipt) (put state 3 completion)
                                       (boundary! rt (when (runtime-field rt :audit)
                                                       {:t :release-request :w (runtime-field rt :world)
                                                        :release (release-id rt) :reason (diagnostic-value (a state 1) true)}))
                                       completion)))
                               (do
                                 (when-let [frame (current-activation)]
                                     ;; Foreign caller admission occurred before this
                                     ;; gate; never acquire its independent gate here.
                                   (when (identical? (runtime-field rt :gate)
                                                     (runtime-field (a frame 0) :gate))
                                     (check-running! (a frame 1))))
                                 (custody-release-preflight! rt)
                                 (when (and (runtime-field rt :parent)
                                            (some #(and (identical? (runtime-field rt :owner-root) (:target-root %))
                                                        (custody-live? %))
                                                  (values (a (runtime-field rt :counters) 7))))
                                   (throw (ex-info "A child requires affine terminal settlement" {:error :capability-open})))
                                 (let [receipt (when-not *custody-terminal-release*
                                                 (NativeReleaseReceipt. (runtime-field rt :owner-root) #?(:clj (Object.) :cljs (js-obj))))
                                       backend (release-context-backend rt)
                                       completion (when receipt (lifecycle/completion backend receipt))]
                                   (put state 1 reason) (put state 2 receipt) (put state 3 completion)
                                   (when completion (swap! pending-releases assoc (runtime-field rt :owner-root) backend))
                                     ;; Retain before any ownership mutation; raw witnesses keep
                                     ;; their immutable first-claim ancestry.
                                   (retain-world-cleanup! rt reason)
                                   (put state 0 :releasing)
                                   (doseq [ob (vec (all-obligations rt)) :when (nil? (a ob o-run))]
                                     (reject-dependent! rt ob {:reason reason}))
                                   (if (custody-state rt)
                                     (binding [*world-release-cancellation* {:reason reason}]
                                       ;; The reference closes explicit Scopes before selecting
                                       ;; surviving direct Root Runs; collateral Run release may
                                       ;; remove other candidates during that Scope cascade.
                                       (each-copy! [scope (custody-order
                                                           (or (scope-children rt (runtime-field rt :owner-root)) empty-members)
                                                           owner-id)]
                                                   (close-owner! rt scope))
                                       (doseq [run (sort-by (comp pr-str run-id)
                                                            (filter #(identical? (runtime-field rt :owner-root) (a % r-owner))
                                                                    (vec (items (a (runtime-field rt :counters) 6)))))]
                                         (cancel! rt run)))
                                     (do
                                       (doseq [run (sort-by #(a % r-gen) > (vec (items (a (runtime-field rt :counters) 6))))]
                                         (retire! rt run {:reason reason :node (a run r-node)}))
                                       (each-copy! [scope (or (scope-children rt (runtime-field rt :owner-root)) empty-members)]
                                                   (close-owner! rt scope))))
                                   (custody-claim-owner! rt (runtime-field rt :owner-root))
                                   (doseq [node (vec (values (runtime-field rt :nodes)))]
                                     (when-let [control (a node n-mailbox)]
                                       (doseq [consumer (vec (concat (values (a control m-pending))
                                                                     (values (a control m-reservations))))]
                                         (refresh-mailbox-owner! rt consumer (a node n-owner))
                                         (when (and (= :host (a consumer b-kind)) (#{:pending :reserved} (a consumer b-state)))
                                           (queue-mailbox-rejection! rt consumer reason :explicit))))
                                     (owner! rt node nil)
                                     (doseq [ob (vec (items (a node n-dependents)))]
                                       (reject-dependent! rt ob {:reason reason}))
                                       ;; Minimal physical run witnesses may still point here.
                                       ;; Ordinary source/body/cache captures do not survive.
                                     (fields! [field [n-body n-descriptor n-value n-public-signal n-deferred n-mailbox
                                                      n-creator n-creator-source n-resume]] (put node field nil))
                                     (clear-members! (a node n-tokens)))
                                   (doseq [id (keys (map-value (a (runtime-field rt :managed-cells) 1)))]
                                     (clear-cell-gc-receipt! rt id))
                                   #?(:clj (.clear ^java.util.Map (runtime-field rt :nodes))
                                      :cljs (.clear (.-buckets (runtime-field rt :nodes))))
                                   #?(:clj (.clear ^java.util.Map (a (runtime-field rt :managed-cells) 0))
                                      :cljs (.clear (.-buckets (a (runtime-field rt :managed-cells) 0))))
                                   (let [events (runtime-field rt :events)
                                         retained (vec (filter (fn [event]
                                                                 (or (custody-event? event)
                                                                     (#{7 9} (alength ^objects event))
                                                                     (not (identical? rt (a (a event 0) n-runtime)))))
                                                               (items events)))]
                                     #?(:clj (.clear ^java.util.ArrayDeque events) :cljs (.clear events))
                                     (doseq [event retained] (push! events event)))
                                   #?(:clj (do (.clear ^java.util.ArrayDeque (runtime-field rt :work))
                                               (.removeIf ^java.util.PriorityQueue (runtime-field rt :ready)
                                                          (reify java.util.function.Predicate
                                                            (test [_ node] (identical? rt (a node n-runtime)))))
                                               (.removeIf ^java.util.ArrayDeque (runtime-field rt :gc)
                                                          (reify java.util.function.Predicate
                                                            (test [_ event] (identical? rt (a event 0))))))
                                      :cljs (do (.clear (runtime-field rt :work))
                                                (let [heap (runtime-field rt :ready)
                                                      retained (.filter heap (fn [node] (not (identical? rt (a node n-runtime)))))]
                                                  (set! (.-length heap) 0)
                                                  (doseq [node (array-seq retained)]
                                                    (ready-add! rt node)))
                                                (.removeWhere (runtime-field rt :gc) (fn [event] (identical? rt (a event 0))))))
                                   (let [live (runtime-field rt :liveness)]
                                     #?(:clj (.clear ^java.util.ArrayDeque (a live 0)) :cljs (.clear (a live 0)))
                                     (fields! [slot [1 2 3]] (clear-members! (a live slot))))
                                   (reset! (runtime-field rt :extension-state) {:values {} :shadowed #{} :map-groups #{}})
                                   (when *custody-terminal-release*
                                     (when-let [parent (runtime-field rt :parent)]
                                       (when (find! (runtime-field parent :nodes) [:fork (runtime-field rt :world)])
                                         (let [n (put (runtime-field parent :counters) 2
                                                      (inc (max (long (a (runtime-field parent :counters) 1))
                                                                (long (a (runtime-field parent :counters) 2)))))]
                                           (push! (runtime-field parent :events)
                                                  (doto (slots 5) (put 0 :fork-released) (put 1 parent) (put 2 parent)
                                                        (put 3 (runtime-field rt :world)) (put 4 n)))))))
                                   (when-not *custody-terminal-release*
                                     (boundary! rt (when (runtime-field rt :audit)
                                                     {:t :release-request :w (runtime-field rt :world)
                                                      :release (release-id rt) :reason (diagnostic-value reason true)})))
                                   completion)))))]
    (when-not *custody-terminal-release*
      (drain! rt dispatch)
      (drain! rt))
    completion))

(defn- lifecycle-await! [requested completion resolve reject]
  (let [rt (canonical-runtime requested)
        release? (satisfies? rtp/PWorldRelease completion)
        target (when release? (rtp/release-runtime completion))]
    (when (and release? (not (instance? OwnedRuntime target)))
      (throw (ex-info "Lifecycle await requires a native completion" {:error :unsupported-operation})))
    (when-not (and (current-activation) (same-cell-world? rt (a (current-activation) 0)))
      (throw (ex-info "Lifecycle await requires ordinary execution" {:error :unsupported-operation})))
    (when release? (release-wait-admission! target))
    (locked rt (check-running! (a (current-activation) 1)))
    (let [resolve (cps-runtime/scope-continuation resolve) reject (cps-runtime/scope-continuation reject)]
      (await-host-effect! (fn [ready failed] (lifecycle/observe! completion ready failed)) resolve reject)
      :org.replikativ.spindel.spin/incomplete)))

(defn- owner-capability [rt owner]
  (cond (root-owner? owner) (ScopeCapability. (runtime-field rt :owner-root) (runtime-field rt :root))
        (scope-owner? owner) (a (owner-storage owner) s-cap)
        :else (ScopeCapability. (runtime-field rt :owner-root)
                                [:run (runtime-field rt :world) (a (a owner r-node) n-id) (a owner r-gen)])))

(defn- owner-cap-id [rt capability]
  (when-not (and (instance? ScopeCapability capability)
                 (identical? (runtime-field rt :owner-root) (.-world ^ScopeCapability capability)))
    (throw (ex-info "Execution owner belongs to another world" {:error :foreign-execution-owner})))
  (.-id ^ScopeCapability capability))

(defn- resolve-owner [rt capability]
  (let [id (when (instance? ScopeCapability capability) (.-id ^ScopeCapability capability))
        state (scope-state rt)
        scope (when state (find! (a state 0) id))
        local? (and (instance? ScopeCapability capability)
                    (identical? (runtime-field rt :owner-root) (.-world ^ScopeCapability capability)))]
    (cond
      (and scope local? (identical? capability (a (owner-storage scope) s-cap))) scope
      (and local? (= id (runtime-field rt :root))) (runtime-field rt :owner-root)
      (and local? (vector? id) (= :run (first id)) (= 4 (count id)))
      (let [node (find! (runtime-field rt :nodes) (nth id 2))
            run (when node (find! (a node n-runs) (nth id 3)))]
        (when-not (and run (open-owner? run) (identical? run (current node)))
          (throw (ex-info "Execution run is not current" {:error :closed-execution-owner})))
        run)
      :else (throw (ex-info "Execution owner is not open in this world"
                            {:error (if local? :closed-execution-owner :foreign-execution-owner)})))))

(defn- local-activation-run [rt]
  (when-let [frame (current-activation)]
    (when (identical? (runtime-field rt :owner-root) (runtime-field (a frame 0) :owner-root))
      (a frame 1))))

(defn- runner-owner-id [rt]
  (when-let [frame (current-activation)]
    (when (identical? (runtime-field rt :owner-root) (runtime-field (a frame 0) :owner-root))
      (if-let [run (a frame 1)]
        [:run (runtime-field rt :world) (a (a run r-node) n-id) (a run r-gen)]
        (when-let [ticket (or (a frame 8) (when-let [operation (active-operation)] (a operation p-ticket)))]
          (when (#{:cps-exit :cps-finalization} (a ticket x-kind))
            (let [[spin generation] (nth (a ticket x-id) 2)]
              [:run (runtime-field rt :world) spin generation])))))))

(defn- copied-owner-root? [rt source spin]
  (when-let [run (local-activation-run rt)]
    (let [node (a run r-node)]
      (and (= spin (a node n-id)) (contains? (:owners (a node n-source-world)) source)))))

(defn capture-execution-owner [requested owner]
  (let [rt (canonical-runtime (execution-runtime requested))]
    (locked rt
            (let [world (runtime-field rt :owner-root) runner (runner-owner-id rt)
                  cap? (instance? ScopeCapability owner)
                  id (when cap? (.-id ^ScopeCapability owner))
                  local? (and cap? (identical? world (.-world ^ScopeCapability owner)))
                  scope (when (and local? (scope-state rt)) (find! (a (scope-state rt) 0) id))]
              (cond
                ;; Only ownership that actually names this activation is a
                ;; contextual Run role. Other saved caps stay literal forever.
                (and runner (or (and (vector? owner) (= owner runner)) (and local? (= id runner))))
                (CapturedOwner. runner :run world (nth runner 2))
                (and local? (= id (runtime-field rt :root)))
                (CapturedOwner. owner :root world (when runner (nth runner 2)))
                (and scope (identical? owner (a (owner-storage scope) s-cap)))
                (CapturedOwner. owner :scope world nil)
                (or (nil? owner) cap? (vector? owner))
                (CapturedOwner. owner :literal nil nil)
                :else (throw (ex-info "Execution owner is not capture data"
                                      {:error :invalid-execution-owner-capture})))))))

(defn restore-execution-owner [requested captured current]
  (let [rt (canonical-runtime (execution-runtime requested))]
    (when-not (instance? CapturedOwner captured)
      (throw (ex-info "Execution owner capture is unavailable" {:error :invalid-execution-owner-capture})))
    (locked rt
            (let [owner (.-owner ^CapturedOwner captured)
                  role (.-role ^CapturedOwner captured)
                  source (.-world ^CapturedOwner captured)
                  spin (.-spin ^CapturedOwner captured)
                  local? (identical? source (runtime-field rt :owner-root))
                  runner (when (= :run role) (runner-owner-id rt))]
              (case role
                :literal owner
                :run (if (and runner (= spin (nth runner 2))
                              (or local? (copied-owner-root? rt source spin)))
                       (if (and (vector? current) (= current runner)) current runner)
                       (ScopeCapability. source owner))
                :root (if (or local? (and spin (copied-owner-root? rt source spin)))
                        (owner-capability rt (runtime-field rt :owner-root))
                        owner)
                :scope (if local?
                         owner
                         (let [id (.-id ^ScopeCapability owner)
                               scope (when-let [state (scope-state rt)] (find! (a state 0) id))]
                           ;; A deleted or never-copied Scope stays qualified by
                           ;; its original world. Restoring data grants no new
                           ;; admission and never fabricates a local Scope row.
                           (if (and scope (some #(identical? owner %) (a (owner-storage scope) 8)))
                             (a (owner-storage scope) s-cap)
                             owner))))))))

(defn- selected-owner [rt]
  (let [frame (current-activation) run (local-activation-run rt) bound ec/*owner-scope*]
    (cond
      ;; An explicit target-world capability is admitted in that world. The
      ;; caller's own owner is merely ambient and defaults to the target root.
      (and frame (not (identical? (runtime-field rt :owner-root)
                                  (runtime-field (a frame 0) :owner-root))))
      (cond
        (and (instance? ScopeCapability bound)
             (identical? (.-world ^ScopeCapability bound) (runtime-field rt :owner-root)))
        (resolve-owner rt bound)
        (or (nil? bound)
            (and (instance? ScopeCapability bound)
                 (identical? (.-world ^ScopeCapability bound) (runtime-field (a frame 0) :owner-root)))
            (and (vector? bound) (= bound (runner-owner-id (a frame 0)))))
        (runtime-field rt :owner-root)
        :else (resolve-owner rt bound))
      (nil? bound) (or run (runtime-field rt :owner-root))
      ;; Runner-installed and CPS-restored Run bindings are pure coordinates;
      ;; only the actual activation can supply their execution authority.
      (and run (vector? bound) (= :run (first bound)) (= 4 (count bound))
           (= (second bound) (runtime-field rt :world))
           (= (nth bound 2) (a (a run r-node) n-id))
           (= (nth bound 3) (a run r-gen))) run
      :else (resolve-owner rt bound))))

(defn root-execution-owner [requested]
  (owner-capability requested (runtime-field requested :owner-root)))

(defn current-execution-owner [requested]
  (let [rt (canonical-runtime requested)]
    (locked rt
            (if (and (instance? ScopeCapability ec/*owner-scope*)
                     (identical? (.-world ^ScopeCapability ec/*owner-scope*) (runtime-field rt :owner-root)))
              ;; Reading restored identity is separate from admitting effects;
              ;; async finally may still name a Scope whose row was reclaimed.
              ec/*owner-scope*
              (owner-capability rt (selected-owner rt))))))

(defn bindable-execution-owner [requested capability]
  (let [rt (canonical-runtime requested)]
    (locked rt
            (world-open! rt)
            (resolve-owner rt capability)
            capability)))

(defn open-execution-scope! [requested kind parent]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested)]
    (locked rt
            (check-computation-caller! rt)
            (world-open! rt)
            (let [owner (resolve-owner rt parent)
                  state (or (scope-state rt)
                            (let [state (doto (slots 4) (put 0 (id-dict)) (put 1 (dict)) (put 2 0) (put 3 0))]
                              (vreset! (runtime-field rt :execution-scopes) state) state))
                  id [:scope :id (a state 2)]
                  capability (ScopeCapability. (runtime-field rt :owner-root) id)
                  data (doto (slots 16) (put s-id id) (put s-cap capability) (put s-kind kind)
                             (put s-open true) (put s-owned (members)) (put s-runs (members)))
                  scope (ScopeOwner. data)
                  run (local-activation-run rt)
                  order (if (and run (identical? owner run))
                          (put (current-activation) 2 (inc (long (a (current-activation) 2)))) 0)]
              (put data s-order order)
              (put state 2 (inc (long (a state 2)))) (put state 3 (inc (long (a state 3))))
              (assoc! (a state 0) id scope) (scope-parent! rt scope owner)
              (when-let [node (owner-node owner)] (mark-graph! rt node) (mark! rt node))
              (boundary! rt (when (runtime-field rt :audit)
                              {:t :t12 :w (runtime-field rt :world) :scope id :parent (owner-id owner)
                               :kind kind :order order}))
              capability))))

(defn- check-scope-close! [rt initial-owner]
  (when-let [service (custody-state rt)]
    (let [index (:index @service) caps (:caps @service)
          ids (loop [todo [initial-owner] seen #{} found #{}]
                (if-let [owner (peek todo)]
                  (if (contains? seen owner) (recur (pop todo) seen found)
                      (let [bucket (find! index (custody-holder rt owner))
                            nodes (when-not (root-owner? owner) (items (a (owner-storage owner) r-owned)))
                            scopes (items (or (scope-children rt owner) empty-members))
                            runs (items (owner-child-runs owner))
                            collateral (mapcat #(values (a % n-runs)) nodes)
                            predecessor (when (and (not (root-owner? owner)) (not (scope-owner? owner))
                                                   (identical? owner (current (a owner r-node))))
                                          (let [p (find! (a (a owner r-node) n-runs) (a owner r-pred))]
                                            (when (and p (= :stale (a p r-status))) [p])))]
                        (recur (into (pop todo) (concat scopes runs collateral predecessor))
                               (conj seen owner) (into found (if bucket (items bucket) []))))) found))
          leaves (map #(find! caps %) ids)]
      (doseq [cap leaves] (custody-shape! rt cap))
      (custody-release-preflight! rt (set (map :target-root leaves))))))

(defn- close-owner! [rt scope]
  (when (and (not (contains? *retiring-owners* scope)) (a (owner-storage scope) s-open))
    (binding [*retiring-owners* (assoc *retiring-owners* scope (run-anchor rt scope))]
      (custody-claim-owner! rt scope)
      (retain-cleanup! rt scope)
      (each-copy! [child (if (custody-state rt)
                           (custody-order (or (scope-children rt scope) empty-members) owner-id)
                           (or (scope-children rt scope) empty-members))] (close-owner! rt child))
      (each-copy! [run (if (custody-state rt)
                         (custody-order (owner-child-runs scope) run-id)
                         (owner-child-runs scope))] (cancel! rt run))
      (release-owned! rt scope)
      (let [data (owner-storage scope) state (scope-state rt) parent (a data s-parent)
            node (owner-node parent)]
        (scope-parent! rt scope nil) (put data s-open false)
        (dissoc! (a state 0) (a data s-id)) (put state 3 (dec (long (a state 3))))
        (clear-members! (a data s-owned)) (clear-members! (a data s-runs)) (put data 8 nil)
        (when node (mark-graph! rt node) (mark! rt node))))))

(defn close-execution-scope! [requested capability]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) id (owner-cap-id rt capability)]
    (when (and (vector? id) (= :run (first id)))
      (throw (ex-info "A Run is closed through cancellation" {:error :invalid-execution-scope})))
    (if (= id (runtime-field rt :root))
      (request-world-release! rt :scope-close)
      (do
        (locked rt
                (when (= :live (a (runtime-field rt :lifecycle) 0))
                  (check-computation-caller! rt)
                  (when-let [scope (when-let [state (scope-state rt)] (find! (a state 0) id))]
                    (when-not (identical? capability (a (owner-storage scope) s-cap))
                      (throw (ex-info "Execution scope capability is unavailable" {:error :foreign-execution-owner})))
                    (check-scope-close! rt scope)
                    (close-owner! rt scope)
                    (boundary! rt (when (runtime-field rt :audit)
                                    {:t :t13 :w (runtime-field rt :world) :scope id})))))
        (drain! rt)))
    nil))

(defn execution-owner-joined? [requested capability]
  (let [rt (canonical-runtime requested) id (owner-cap-id rt capability)
        id (if (and (vector? id) (= :run (first id))) [(nth id 2) (nth id 3)] id)]
    (join-ready? rt id)))

;; Family-local affine custody. This service is allocated only by publication;
;; saved authority contains identities and IDs, never borrowed arena storage.
(defn- custody-order [members key-fn]
  (let [ordered (sort-by (comp pr-str key-fn) (items members))]
    #?(:clj (java.util.ArrayList. ^java.util.Collection ordered)
       :cljs (into-array ordered))))
(defn- custody-state [rt]
  (let [state (a (runtime-field rt :counters) 11)]
    (when-not (map? state) state)))
(defn- custody-state! [rt]
  (or (custody-state rt)
      (let [index (or (a (runtime-field rt :counters) 10) (id-dict))
            state (volatile! {:claims {} :records {} :next-claim 0 :pending {} :targets {} :phases {} :worlds (runtime-field rt :family) :caps (a (runtime-field rt :counters) 7) :index index :refreshing? false})]
        (put (runtime-field rt :counters) 10 index)
        (put (runtime-field rt :counters) 11 state)
        state)))
(defn- custody-world-phase [rt]
  (when-let [state (custody-state rt)] (get-in @state [:phases (runtime-field rt :owner-root)])))
(defn- custody-holder [rt owner]
  (->CustodyHolder (runtime-field rt :owner-root) (runtime-field rt :world)
                   (cond (root-owner? owner) :root (scope-owner? owner) :scope :else :run)
                   (owner-id owner)))
(defn- custody-owner-holds? [rt owner]
  (when (a (runtime-field rt :counters) 11)
    (when-let [bucket (find! (a (runtime-field rt :counters) 10) (custody-holder rt owner))]
      (pos? (count! bucket)))))
(defn- custody-holder-view [holder]
  (if (instance? CustodyHolder holder)
    [:execution-owner (:world holder) (:kind holder) (:id holder)] holder))
(defn- custody-cap-view [cap]
  (select-keys cap [:world :scope :holder :holder-acquisition :disposition :published?
                    :op :pred :successors :durable? :bases :kind]))
(defn- custody-project [rt]
  (let [service (or (custody-state rt) (:service *custody-frame*))
        state (some-> service deref)]
    {:custody {:by-holder (if-let [index (or (:index state) (a (runtime-field rt :counters) 10))]
                            (into {} (for [[holder bucket] (map-value index)]
                                       [(custody-holder-view holder) (set (items bucket))])) {})
               :claims (into {} (for [[id claim] (:claims state)]
                                  [id (dissoc claim :origin-key)]))}
     :records (or (:records state) {}) :next-claim (or (:next-claim state) 0)}))
(defn- custody-live? [cap]
  (contains? #{:open :sealed :settling :incomplete} (:disposition cap)))
(defn- custody-put! [rt id cap]
  (let [state (some-> (or (custody-state rt) (:service *custody-frame*)) deref)
        caps (or (:caps state) (a (runtime-field rt :counters) 7))
        index (or (:index state) (a (runtime-field rt :counters) 10))
        previous (find! caps id)]
    (when (and previous (custody-live? previous))
      (when-let [bucket (find! index (:holder-key previous))]
        (remove! bucket id)
        (when (zero? (count! bucket)) (dissoc! index (:holder-key previous)))))
    (assoc! caps id cap)
    (when (custody-live? cap)
      (add! (or (find! index (:holder-key cap)) (assoc! index (:holder-key cap) (members))) id))
    cap))
(defn- custody-operation-reserved? [rt op]
  (or (nil? op)
      (contains? (:records @(custody-state! rt)) op)
      (some #(= op (:op %)) (values (a (runtime-field rt :counters) 7)))
      (some #(= op (:settlement-op %)) (vals (:claims @(custody-state! rt))))))
(defn- custody-fresh-operation! [rt op]
  (when (custody-operation-reserved? rt op)
    (throw (ex-info "Operation identity is already reserved" {:error :op-exists :op op})))
  op)
(defn- custody-owner-acquisition [rt owner]
  (world-open! rt)
  (cond (or (root-owner? owner) (scope-owner? owner)) nil
        :else
        (let [node (a owner r-node) status (a owner r-status)]
          (when-not (and (identical? owner (current node))
                         (or (#{:running :parked} status) (and (= :completed status) (reactive? owner))))
            (throw (ex-info "Custody destination is not an admitted current owner" {:error :invalid-destination})))
          (if (= :running status)
            (let [frame (current-activation)]
              (when-not (and frame (same-cell-world? rt (a frame 0)) (identical? owner (a frame 1)))
                (throw (ex-info "Custody acceptance requires destination activation" {:error :missing-destination-order})))
              (inc (long (a frame 2))))
            :exact-run))))
(defn- custody-commit-order! [order]
  (when (integer? order) (put (current-activation) 2 order)))
(defn- custody-publication-owner [rt options]
  (let [owner (if-let [cap (:owner options)] (resolve-owner rt cap) (selected-owner rt))]
    (custody-owner-acquisition rt owner)
    owner))
(defn- custody-publish! [rt child owner id]
  (let [service (custody-state! rt) holder (custody-holder rt owner)
        order (custody-owner-acquisition rt owner) token #?(:clj (Object.) :cljs (js-obj))]
    (put (runtime-field child :counters) 10 (a (runtime-field rt :counters) 10))
    (put (runtime-field child :counters) 11 service)
    (custody-put! rt id {:world (runtime-field child :world) :target-root (runtime-field child :owner-root)
                         :scope #{} :holder (custody-holder-view holder) :holder-key holder
                         :holder-acquisition order :disposition :open :published? true
                         :op nil :pred nil :successors [] :durable? false :bases {} :token token})
    (custody-commit-order! order)
    (NativeWorldCapability. (runtime-field rt :family-id) id token)))
(defn- custody-bearer! [rt bearer phases]
  (when-not (and (instance? NativeWorldCapability bearer)
                 (identical? (runtime-field rt :family-id) (.-family ^NativeWorldCapability bearer)))
    (throw (ex-info "Capability belongs to another family" {:error :stale-capability})))
  (let [id (.-id ^NativeWorldCapability bearer) cap (find! (a (runtime-field rt :counters) 7) id)]
    (when-not (and cap (identical? (:token cap) (.-token ^NativeWorldCapability bearer))
                   (contains? phases (:disposition cap)))
      (throw (ex-info "Capability has been consumed" {:error :stale-capability})))
    [id cap]))
(defn- custody-caller! [rt cap caller]
  (let [owner (resolve-owner rt caller) holder (custody-holder rt owner)]
    (when (and (not (or (root-owner? owner) (scope-owner? owner)))
               (not (or (#{:running :parked} (a owner r-status))
                        (and (= :completed (a owner r-status)) (reactive? owner)))))
      (throw (ex-info "Caller Run is not admitted" {:error :stale-capability})))
    (when-not (= holder (:holder-key cap))
      (throw (ex-info "Caller does not hold this capability" {:error :stale-capability})))
    holder))
(defn fork-owned-world! [requested options]
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) world (get options :world-id [:w (random-uuid)])]
    (when (or (not= #{} (get options :systems #{})) (not= :following (get options :mode :following))
              (seq (dissoc options :world-id :owner :systems :mode)))
      (throw (ex-info "Native fork options are outside this profile" {:error :unsupported-operation :operation :fork-options})))
    (locked rt
            (world-open! rt)
            (let [owner (custody-publication-owner rt options) id [:cap (random-uuid)]
                  child (fork-custody-copy! rt world owner id)
                  cap (find! (a (runtime-field rt :counters) 7) id)]
              {:context child :capability (NativeWorldCapability. (runtime-field rt :family-id) id (:token cap))}))))
(defn fork-parked! [rt world]
  (:context (fork-owned-world! rt {:world-id world})))
(defn transfer-owned-world! [requested bearer caller destination acceptor options]
  (admit-native-effect!)
  (when (seq (dissoc options :operation-id))
    (throw (ex-info "Unsupported custody transfer options" {:error :unsupported-operation})))
  (when-not (and (instance? OwnedRuntime requested) (instance? OwnedRuntime destination)
                 (identical? (:family-id requested) (:family-id destination)))
    (throw (ex-info "Independent-family custody requires a coordinator" {:error :unsupported-operation :operation :cross-family-custody})))
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) dest (canonical-runtime destination)]
    (locked rt
            (check-native-caller! rt)
            (let [[id cap] (custody-bearer! rt bearer #{:open})
                  from (custody-caller! rt cap caller) owner (resolve-owner dest acceptor)
                  holder (custody-holder dest owner) order (custody-owner-acquisition dest owner)
                  _ (when (seq (:scope cap))
                      (throw (ex-info "Nonempty settlement scopes require later integration" {:error :unsupported-operation})))
                  _ (when (or (custody-automatic-holder? rt holder)
                              (contains? (custody-protected-roots rt) (runtime-field dest :owner-root)))
                      (custody-disposal-preflight! rt cap))
                  op (get options :operation-id [:transfer (random-uuid)])
                  _ (custody-fresh-operation! rt op) successor [:cap (random-uuid)]
                  token #?(:clj (Object.) :cljs (js-obj)) service (custody-state! rt)]
              (vswap! service assoc-in [:records op]
                      {:op op :cap id :kind :transfer :payload-hash {:successor successor :holder (custody-holder-view holder)}
                       :steps [] :bases {} :effects-released? true})
              (custody-put! rt id (assoc cap :disposition :transferred :op op :successors [successor]))
              (custody-put! rt successor (assoc cap :holder-key holder :holder (custody-holder-view holder)
                                                :holder-acquisition order :pred id :op nil :successors [] :token token))
              (custody-commit-order! order)
              (boundary! rt (when (runtime-field rt :audit)
                              (cond-> {:t :t32 :k id :successor successor :op op
                                       :caller (custody-holder-view from) :holder (custody-holder-view holder)
                                       :acceptor (custody-holder-view holder)}
                                (integer? order) (assoc :acceptance {:th :engine :order order}))))
              (NativeWorldCapability. (runtime-field rt :family-id) successor token)))))

(declare observe-disposal-backend!)
(deftype ^:private NativeDisposalBackend [state]
  rtp/PWorldCustody
  (fork-owned-world! [_ _] (throw (ex-info "Completion grants no custody" {:error :unsupported-operation})))
  (transfer-owned-world! [_ _ _ _ _ _] (throw (ex-info "Completion grants no custody" {:error :unsupported-operation})))
  (discard-owned-world! [_ _ _ _] (throw (ex-info "Completion grants no custody" {:error :unsupported-operation})))
  (observe-owned-world-disposal! [_ receipt resolve reject] (observe-disposal-backend! state receipt resolve reject)))
(defn- disposal-notify! [state id]
  (let [observer (loop []
                   (let [before @state observer (when (:done? before) (get-in before [:observers id]))]
                     (when observer
                       (if (compare-and-set! state before (update before :observers dissoc id))
                         observer (recur)))))]
    (when-let [[resolve context] observer]
      (host-callback-scope context #(binding [cps/*in-trampoline* false]
                                      (cps/with-trampoline (cps/invoke-continuation resolve %))) nil))))

(defn- observe-disposal-backend! [state receipt resolve _reject]
  (let [before @state]
    (when-not (identical? receipt (:receipt before))
      (throw (ex-info "Foreign disposal receipt" {:error :foreign-disposal-receipt})))
    (when-let [frame (current-activation)]
      (let [target (:runtime before)
            roots (if target (locked target (custody-reachable-roots target false))
                      #{(.-target ^NativeDiscardReceipt receipt)})]
        (when (contains? roots (runtime-field (a frame 0) :owner-root))
          (throw (ex-info "Disposal cannot await a physical frame in its target cleanup closure" {:error :self-discard-join}))))
      (when (or (active-operation) (active-mailbox-callback))
        (throw (ex-info "Protected callbacks cannot observe ordinary disposal" {:error :cleanup-only})))
      (locked (a frame 0) (check-running! (a frame 1))))
    (let [id (random-uuid) resolve (cps-runtime/scope-continuation resolve)]
      (swap! state assoc-in [:observers id] [resolve ec/*execution-context*])
      (when (:done? @state) (disposal-notify! state id))
      (fn [] (swap! state update :observers dissoc id) nil))))
(defn observe-owned-world-disposal! [_ _ _ _]
  (throw (ex-info "Disposal observations require their typed backend" {:error :foreign-disposal-receipt})))
(defn- custody-target! [rt cap]
  (let [target (find! (runtime-field rt :family) (:world cap))]
    (when-not (and target (identical? (:target-root cap) (runtime-field target :owner-root)))
      (throw (ex-info "Capability target is unavailable" {:error :missing-world})))
    target))
(defn- custody-shape! [rt cap]
  (let [target (custody-target! rt cap)]
    (when (or (seq (:scope cap))
              (and (not= :open (:disposition cap))
                   (or (not= :discard (:kind cap))
                       (seq (:steps (get-in @(custody-state! rt) [:records (:op cap)])))))
              (not (empty-dict? (a (runtime-field target :timers) 0)))
              (some #(contains? #{:deferred :mailbox} (a % n-kind)) (values (runtime-field target :nodes))))
      (throw (ex-info "Target resources require later custody integration"
                      {:error :unsupported-operation :operation :custody-resource-profile})))))
(defn- custody-disposal-preflight! [rt cap]
  (custody-shape! rt cap)
  (custody-release-preflight! rt [(:target-root cap)]))

(defn- custody-automatic-holder? [rt holder]
  (when (instance? CustodyHolder holder)
    (case (:kind holder)
      :run true
      :scope
      (let [service (custody-state rt) world (find! (:worlds @service) (:world holder))
            state (when (and world (not (custody-data-world? world))
                             (identical? (:root holder) (runtime-field world :owner-root)))
                    (scope-state world))
            scope (when state (find! (a state 0) (:id holder)))]
        (when-not scope
          (throw (ex-info "Custody holder Scope is absent" {:error :invalid-custody-holder})))
        (loop [owner (owner-parent scope)]
          (cond (nil? owner) false
                (root-owner? owner) false
                (scope-owner? owner) (recur (owner-parent owner))
                :else true)))
      false)))

(defn- custody-protected-roots [rt]
  (when-let [service (custody-state rt)]
    (let [state @service caps (:caps state)
          seeds (set (concat
                      (for [[_ claim] (:claims state) :let [cap (find! caps (:cap claim))]] (:target-root cap))
                      (for [[_ debts] (:targets state) [_ debt] debts] (:target-root debt))
                      (for [[id _] (:pending state) :let [cap (find! caps id)] :when (custody-live? cap)] (:target-root cap))
                      (for [cap (values caps)
                            :when (and (custody-live? cap) (custody-automatic-holder? rt (:holder-key cap)))]
                        (:target-root cap))))]
      (custody-reachable-roots rt true seeds))))

(defn- custody-resource-ingress! [rt]
  ;; Called under the shared family gate before resource/cursor/transport
  ;; admission. No scan or additional allocation in worlds without custody.
  (when (and (custody-state rt)
             (contains? (custody-protected-roots rt) (runtime-field rt :owner-root)))
    (throw (ex-info "New resources are outside preserved custody cleanup profile"
                    {:error :unsupported-operation :operation :custody-resource-ingress}))))

(defn- custody-pending! [rt id cap]
  (let [service (custody-state! rt)]
    (or (get-in @service [:pending id])
        (let [target (custody-target! rt cap)
              receipt (NativeDiscardReceipt. (:target-root cap) #?(:clj (Object.) :cljs (js-obj)))
              state (atom {:receipt receipt :done? false :observers {} :runtime target :service service})
              completion (lifecycle/discard-completion (NativeDisposalBackend. state) receipt)
              pending {:cap id :target target :state state :completion completion :phase :preparing}]
          (vswap! service assoc-in [:pending id] pending)
          (assoc! (a (runtime-field rt :counters) 7) id (assoc cap :completion completion))
          pending))))
(defn- custody-event? [event] (contains? #{:custody :fork-released} (a event 0)))
(defn- custody-event-view [event]
  (if (= :fork-released (a event 0))
    {:fork-released (a event 3) :seq (a event 4)}
    (let [rt (a event 1) id (a event 3) claim (get-in @(custody-state rt) [:claims id])]
      {:custody-dispatch id :cap (or (:cap claim) (a event 5))
       :op (or (:settlement-op claim) (a event 6)) :seq (a event 4)})))

(defn- custody-claim-owner! [rt owner]
  (when-let [service (custody-state rt)]
    (let [holder (custody-holder rt owner) bucket (find! (a (runtime-field rt :counters) 10) holder)]
      (doseq [id (sort-by pr-str (if bucket (vec (items bucket)) []))]
        (let [cap (find! (a (runtime-field rt :counters) 7) id)
              [claim-id op] (loop [n (:next-claim @service)]
                              (let [claim [:custody-claim n] op (or (:op cap) [:custody-op claim])]
                                (if (or (contains? (:claims @service) claim)
                                        (and (nil? (:op cap)) (custody-operation-reserved? rt op)))
                                  (recur (inc n))
                                  (do (vswap! service assoc :next-claim (inc n)) [claim op]))))
              claim {:cap id :holder [:cleanup claim-id] :origin (custody-holder-view holder) :origin-key holder
                     :anchor (mapv (fn [local]
                                     [:execution-owner (runtime-field rt :world)
                                      (cond (= local (runtime-field rt :root)) :root
                                            (and (vector? local) (= 3 (count local))
                                                 (= [:scope :id] (subvec local 0 2))) :scope :else :run) local])
                                   (butlast (run-anchor rt owner)))
                     :target-world (:world cap) :kind :discard :settlement-op op :phase :dispatch-pending}
              target (custody-target! rt cap)]
          (custody-pending! rt id cap)
          (vswap! service assoc-in [:claims claim-id] claim)
          (vswap! service assoc-in [:targets (:root holder) claim-id]
                  {:origin-world (runtime-field rt :world) :target-world (:world cap)
                   :target-root (:target-root cap) :cap id :op op})
          (custody-put! rt id (assoc (find! (a (runtime-field rt :counters) 7) id)
                                     :holder [:cleanup claim-id] :holder-key [:cleanup claim-id] :holder-acquisition nil))
          (let [seqno (put (runtime-field target :counters) 2
                           (inc (max (long (a (runtime-field target :counters) 1))
                                     (long (a (runtime-field target :counters) 2)))))]
            (push! (runtime-field rt :events)
                   (doto (slots 8) (put 0 :custody) (put 1 rt) (put 2 target) (put 3 claim-id) (put 4 seqno)
                         (put 5 id) (put 6 op) (put 7 (:token cap))))))))))
(defn- custody-adopt! [rt previous successor order]
  (when-let [_ (custody-state rt)]
    (let [holder (custody-holder rt previous) dest (custody-holder rt successor)
          bucket (find! (a (runtime-field rt :counters) 10) holder)]
      (doseq [id (if bucket (vec (items bucket)) [])
              :let [cap (find! (a (runtime-field rt :counters) 7) id) acquisition (:holder-acquisition cap)]
              :when (and (integer? acquisition) (< acquisition order))]
        (custody-put! rt id (assoc cap :holder-key dest :holder (custody-holder-view dest)))))))
(defn- custody-reachable-roots
  ([rt prospective?] (custody-reachable-roots rt prospective? [(runtime-field rt :owner-root)]))
  ([rt prospective? seeds]
   (let [service (or (custody-state rt) (:service *custody-frame*)) state (some-> service deref)
         caps (:caps state)]
     (loop [todo (vec seeds) seen #{}]
       (if-let [root (peek todo)]
         (if (contains? seen root) (recur (pop todo) seen)
             (let [held (when (and prospective? caps)
                          (for [cap (values caps)
                                :when (and (custody-live? cap) (instance? CustodyHolder (:holder-key cap))
                                           (identical? root (:root (:holder-key cap))))] (:target-root cap)))
                   debts (map :target-root (vals (get-in state [:targets root])))]
               (recur (into (pop todo) (concat held debts)) (conj seen root)))) seen)))))

(defn- custody-release-preflight!
  ([rt] (custody-release-preflight! rt [(runtime-field rt :owner-root)]))
  ([rt seeds]
   (let [service (custody-state rt) state (some-> service deref)
         required (custody-reachable-roots rt true seeds)
         caps (or (:caps state) (a (runtime-field rt :counters) 7))
         selected (concat
                   (for [cap (values caps)
                         :when (and (instance? CustodyHolder (:holder-key cap))
                                    (contains? required (:root (:holder-key cap))))] cap)
                   (for [root required [_ debt] (get-in state [:targets root])] (find! caps (:cap debt))))]
     (doseq [cap selected :when (custody-live? cap)]
       (custody-shape! rt cap)
       (when-not (and (empty? (:scope cap))
                      (or (= :open (:disposition cap))
                          (and (= :discard (:kind cap))
                               (empty? (:steps (get-in state [:records (:op cap)]))))))
         (throw (ex-info "Settlement executor is outside this custody profile"
                         {:error :unsupported-operation :operation :custody-settlement}))))
    ;; The bounded native fork profile has no foreign entity handshake.
    ;; Inspect both directions only when an endpoint is in this closure.
     (doseq [world (values (or (:worlds state) (runtime-field rt :family)))
             :when (not (custody-data-world? world))
             ob (all-obligations world)
             :let [debtor (a ob o-debtor) creditor (a ob o-creditor-node)
                   debtor-rt (when debtor (a debtor n-runtime))
                   creditor-rt (when creditor (a creditor n-runtime))
                   involved? (or (contains? required (runtime-field world :owner-root))
                                 (and debtor-rt (contains? required (runtime-field debtor-rt :owner-root)))
                                 (and creditor-rt (contains? required (runtime-field creditor-rt :owner-root))))]
             :when involved?]
       (when (or (and debtor-rt (not (same-cell-world? world debtor-rt)))
                 (and creditor-rt (not (same-cell-world? world creditor-rt))))
         (throw (ex-info "Foreign entity obligations require the coordinated lifecycle"
                         {:error :unsupported-operation :operation :world-release-lineage})))))))

(defn- custody-release-ready? [rt]
  (let [service (or (custody-state rt) (:service *custody-frame*)) state (some-> service deref)
        caps (:caps state) worlds (:worlds state)]
    (loop [todo [rt] seen #{}]
      (if-let [world (peek todo)]
        (let [data? (custody-data-world? world)
              root (if data? (:root world) (runtime-field world :owner-root)) todo (pop todo)]
          (cond
            (contains? seen root) (recur todo seen)
            (and (not data?)
                 (or (= :live (a (runtime-field world :lifecycle) 0))
                     (not (join-ready? world (runtime-field world :root))))) false
            :else
            (let [debts (vals (get-in state [:targets root]))
                  destinations (map #(when worlds (find! worlds (:target-world %))) debts)]
              (if (or (some nil? destinations)
                      (some (fn [debt]
                              (let [cap (when caps (find! caps (:cap debt)))
                                    record (get-in state [:records (:op debt)])]
                                (not (and (= :discarded (:disposition cap)) (= (:op debt) (:op cap))
                                          (= (:cap debt) (:cap record)) (:effects-released? record))))) debts))
                false
                (recur (into todo destinations) (conj seen root)))))) true))))
(defn- custody-debts? [rt] (not (custody-release-ready? rt)))
(defn- custody-targets-view [rt]
  (let [service (or (custody-state rt) (:service *custody-frame*))]
    (into {} (for [[_ debts] (:targets (some-> service deref)) :when (seq debts)]
               [(:origin-world (val (first debts)))
                (into {} (for [[id debt] debts] [id (select-keys debt [:target-world :cap :op])]))]))))

(defn- custody-seal! [rt id cap op action]
  (let [service (custody-state! rt) target (custody-target! rt cap)
        pending (custody-pending! rt id cap)]
    ;; Seal before cancellation can claim this cap through its own target Run.
    (custody-put! rt id (assoc (find! (a (runtime-field rt :counters) 7) id)
                               :disposition :sealed :kind :discard :op op))
    (vswap! service assoc-in [:phases (:target-root cap)]
            {:seal-seq nil :cap id})
    (doseq [run (vec (items (a (runtime-field target :counters) 6)))
            :when (work-status? (a run r-status))] (cancel! target run))
    (vswap! service assoc-in [:phases (:target-root cap) :seal-seq]
            (max (long (a (runtime-field target :counters) 1)) (long (a (runtime-field target :counters) 2))))
    (boundary! target (when (runtime-field target :audit) action))
    pending))
(defn discard-owned-world! [requested bearer caller options]
  (admit-native-effect!)
  (when (seq (dissoc options :operation-id))
    (throw (ex-info "Unsupported discard options" {:error :unsupported-operation})))
  (admit-world-switch! requested)
  (let [rt (canonical-runtime requested) dispatch @(runtime-field rt :arena-cell)
        completion (locked rt
                           (check-native-caller! rt)
                           (let [[id cap] (custody-bearer! rt bearer #{:open :sealed :settling :discarded})]
                             (if (and (:completion cap) (not= :open (:disposition cap)))
                               (do (when (and (contains? options :operation-id)
                                              (not= (:operation-id options) (:op cap)))
                                     (throw (ex-info "Discard operation changed" {:error :changed-operation})))
                                   (:completion cap))
                               (let [_ (custody-disposal-preflight! rt cap)
                                     _ (custody-caller! rt cap caller)
                                     op (get options :operation-id [:discard (random-uuid)])
                                     _ (custody-fresh-operation! rt op)]
                                 (:completion (custody-seal! rt id cap op
                                                             {:t :t26 :k id :op op :kind :discard :caller (:holder cap)}))))))]
    (drain! rt dispatch)
    (drain! rt)
    completion))
(defn- custody-dispatch! [rt event]
  (if (= :fork-released (a event 0))
    (do (when-let [node (find! (runtime-field rt :nodes) [:fork (a event 3)])]
          (owner! rt node nil) (mark! rt node))
        (boundary! rt (when (runtime-field rt :audit) {:t :t36 :w (runtime-field rt :world)})))
    (let [claim-id (a event 3) service (custody-state! rt) claim (get-in @service [:claims claim-id])
          target (a event 2)]
      (if-not claim
        (let [cap (find! (a (runtime-field rt :counters) 7) (a event 5))
              record (get-in @service [:records (a event 6)])]
          (when-not (and (= :discarded (:disposition cap)) (= [:cleanup claim-id] (:holder-key cap))
                         (= (a event 6) (:op cap)) (= (a event 5) (:cap record))
                         (:effects-released? record) (identical? (a event 7) (:token cap)))
            (throw (ex-info "Custody dispatch lost its claim" {:error :invalid-custody-claim})))
          (boundary! target (when (runtime-field target :audit) {:t :queued :w (runtime-field target :world)})))
        (let [id (:cap claim) cap (find! (a (runtime-field rt :counters) 7) id)]
          (when-not (and (= [:cleanup claim-id] (:holder-key cap)) (= :dispatch-pending (:phase claim))
                         (= id (a event 5)) (= (:settlement-op claim) (a event 6))
                         (identical? (a event 7) (:token cap)))
            (throw (ex-info "Custody dispatch does not own its leaf" {:error :invalid-custody-claim})))
          (vswap! service assoc-in [:claims claim-id :phase] :active)
          (if (= :open (:disposition cap))
            (custody-seal! rt id cap (:settlement-op claim) {:t :queued :w (runtime-field target :world)})
            (boundary! target (when (runtime-field target :audit) {:t :queued :w (runtime-field target :world)}))))))))

(defn- refresh-custody-releases! [rt]
  ;; End-of-action publication is independent of settlement advancement. In
  ;; particular T29 must expose debt pruning and ALL newly joined receipts in
  ;; its own audit boundary, even while the settlement driver is reentrant.
  (when-let [service (or (custody-state rt) (:service *custody-frame*))]
    (let [worlds (vec (values (:worlds @service)))
          ready (set (for [world worlds
                           :when (or (custody-data-world? world) (custody-release-ready? world))]
                       (if (custody-data-world? world) (:root world) (runtime-field world :owner-root))))]
      (vswap! service update :targets
              (fn [targets]
                (into {} (keep (fn [[origin debts]]
                                 (let [remaining (into {} (remove (fn [[_ debt]]
                                                                    (contains? ready (:target-root debt))) debts))]
                                   (when (seq remaining) [origin remaining]))) targets))))
      (doseq [world worlds :when (not (custody-data-world? world))]
        (refresh-release! world)
        (custody-release-data! world)))))

(defn- refresh-custody! [rt]
  (when-let [service (or (custody-state rt) (:service *custody-frame*))]
    (when-not (:refreshing? @service)
      (vswap! service assoc :refreshing? true)
      (try
        (binding [*custody-frame* {:service service :family (:worlds @service)}]
          (loop []
            (let [before (:pending @service)]
              (doseq [[id pending] before
                      :let [cap (find! (:caps @service) id) target (:target pending)]
                      :when (and (= :preparing (:phase pending)) (= :sealed (:disposition cap))
                                 (or (not= :cleanup (first (:holder cap)))
                                     (= :active (get-in @service [:claims (second (:holder cap)) :phase])))
                                 (join-ready? target (runtime-field target :root)))]
                (let [op (:op cap)
                      record {:op op :cap id :kind :discard :payload-hash nil :steps [] :bases {} :effects-released? false}]
                  (vswap! service assoc-in [:records op] record)
                  (custody-put! rt id (assoc cap :disposition :settling))
                  (boundary! target (when (runtime-field target :audit)
                                      {:t :t27 :k id :op op :steps [] :bases {} :payload nil}))
                  (custody-put! rt id (assoc (find! (:caps @service) id) :disposition :discarded))
                  (vswap! service assoc-in [:records op :effects-released?] true)
                  (vswap! service update :claims
                          #(into {} (remove (fn [[_ claim]] (= id (:cap claim))) %)))
                ;; Keep causal target debt until its composed release, not T29.
                  (vswap! service assoc-in [:pending id :phase] :releasing)
                  (binding [*custody-terminal-release* true] (request-world-release! target :discard))
                  (refresh-release! target)
                  (boundary! target (when (runtime-field target :audit) {:t :t29 :op op}))))
              (refresh-custody-releases! rt)
              (doseq [[id pending] (:pending @service)
                      :when (and (= :releasing (:phase pending))
                                 (custody-release-ready? (:target pending)))]
                (let [cell (:state pending)]
                  (vswap! service update :pending dissoc id)
                  (swap! cell #(-> % (assoc :done? true) (dissoc :runtime :service)))
                  (doseq [observer (keys (:observers @cell))]
                    (push! (runtime-field rt :posts) (doto (slots 1) (put 0 #(disposal-notify! cell observer)))))))
              (refresh-custody-releases! rt)
              (when (not= before (:pending @service)) (recur)))))
        (finally (vswap! service assoc :refreshing? false))))))

(defn- custody-data-world? [world] (and (map? world) (true? (:custody-tombstone world))))
(defn- custody-release-data! [rt]
  (let [state (runtime-field rt :lifecycle)]
    (when (or (a state 6) (not= :live (a state 0)))
      (when-not (a state 6) (put state 6 (volatile! nil)))
      (vreset! (a state 6) (when (a state 3) (release-observer-row rt))))))
(defn- custody-audit-family [rt]
  (custody-release-data! rt)
  (if (or *custody-frame* (not= :joined (a (runtime-field rt :lifecycle) 0)))
    (snapshot-family rt)
    (let [prior (some-> (runtime-field rt :audit) deref last (nth 2 nil))
          local (snapshot rt)]
      (if (and prior (contains? prior (runtime-field rt :world)))
        (let [family (assoc prior (runtime-field rt :world)
                            (merge (select-keys (first (vals prior)) [:global :handles :threads :gc :principals :cleanup-targets])
                                   (dissoc local :global :handles :threads :gc :principals :cleanup-targets)))
              registry (set (for [[id world] family :when (not= :released (:status world))] id))]
          (into {} (for [[id world] family] [id (assoc-in world [:global :registry] registry)])))
        (snapshot-family rt)))))
