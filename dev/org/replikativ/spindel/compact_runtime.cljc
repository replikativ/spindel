(ns org.replikativ.spindel.compact-runtime
  "Experimental owned-object CPS engine. Canonical maps are diagnostic output,
  never the live representation. Supports the local reactive lifetime slice."
  (:refer-clojure :exclude [await assoc! dissoc! pop!])
  #?(:cljs (:require-macros [org.replikativ.spindel.compact-runtime :refer [locked each! each-copy!]]))
  (:require [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.incremental.interval :as iv]
            #?(:clj [org.replikativ.spindel.spin.cps :as compiler])))

(def ^:dynamic *activation* nil)
(defn- a [xs i] (aget ^objects xs i))
(defn- put [xs i value] (aset ^objects xs i value) value)
(defn- slots [n] #?(:clj (object-array n) :cljs (make-array n)))
#?(:cljs (deftype IDMap [buckets]))
(defn- dict [] #?(:clj (java.util.HashMap.) :cljs (js/Map.)))
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
(defn- members [] #?(:clj (java.util.HashSet.) :cljs (js/Set.)))
(defn- add! [s x] #?(:clj (.add ^java.util.Set s x) :cljs (.add s x)))
(defn- remove! [s x] #?(:clj (.remove ^java.util.Set s x) :cljs (.delete s x)))
(defn- has? [s x] #?(:clj (.contains ^java.util.Set s x) :cljs (.has s x)))
(defn- items [s] #?(:clj (seq s) :cljs (array-seq (js/Array.from s))))
(defn- values [m]
  #?(:clj (.values ^java.util.Map m)
     :cljs (if (instance? IDMap m)
             (let [result (array)]
               (.forEach (.-buckets m)
                         (fn [bucket] (loop [i 1]
                                        (when (< i (.-length bucket))
                                          (.push result (aget bucket i)) (recur (+ i 2))))))
               result)
             (.values m))))
(defn- count! [s] #?(:clj (.size ^java.util.Collection s) :cljs (.-size s)))
(defn- queue [] #?(:clj (java.util.ArrayDeque.) :cljs (array)))
(defn- push! [q x] #?(:clj (.addLast ^java.util.ArrayDeque q x) :cljs (.push q x)))
(defn- pop! [q] #?(:clj (.pollFirst ^java.util.ArrayDeque q) :cljs (.shift q)))
(defn- queued? [q] #?(:clj (not (.isEmpty ^java.util.ArrayDeque q)) :cljs (pos? (.-length q))))

(def ^:private empty-array #?(:clj (object-array 0) :cljs (array)))
(defn- copy-items [xs]
  #?(:clj (.toArray ^java.util.Collection xs ^objects empty-array)
     :cljs (js/Array.from xs)))
(defn- any! [xs pred]
  #?(:clj (let [it (.iterator ^java.lang.Iterable xs)]
            (loop [] (when (.hasNext it)
                       (let [x (.next it)] (if (pred x) true (recur))))))
     :cljs (let [it (js* "~{}[Symbol.iterator]()" xs)]
             (loop [] (let [entry (.next it)]
                        (when-not (.-done entry)
                          (if (pred (.-value entry)) true (recur))))))))

#?(:clj
   (do
     (defmacro each! [[x xs] & body]
       (if (:ns &env)
         `(let [it# (~'js* "~{}[Symbol.iterator]()" ~xs)]
            (loop [] (let [entry# (.next it#)]
                       (when-not (.-done entry#)
                         (let [~x (.-value entry#)] ~@body) (recur)))))
         `(let [^java.lang.Iterable coll# ~xs
                ^java.util.Iterator it# (.iterator coll#)]
            (while (.hasNext it#) (let [~x (.next it#)] ~@body)))))
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
(def ^:const r-node 0) (def ^:const r-gen 1) (def ^:const r-owner 2)
(def ^:const r-pred 3) (def ^:const r-status 4) (def ^:const r-created 5)
(def ^:const r-spawned 6) (def ^:const r-seq 7) (def ^:const r-obs 8)
(def ^:const r-owned 9) (def ^:const r-backlinks 10) (def ^:const r-childruns 11) (def ^:const r-physical 12) (def ^:const r-anchor 13)
(def ^:const o-id 0) (def ^:const o-kind 1) (def ^:const o-debtor 2)
(def ^:const o-run 3) (def ^:const o-standing 4) (def ^:const o-resolve 5)
(def ^:const o-reject 6) (def ^:const o-order 7) (def ^:const o-slot 8)
(def ^:const o-success 9) (def ^:const o-failure 10) (def ^:const o-last 11)
(def ^:const o-live 12) (def ^:const o-value 13)
(def ^:const t-id 0) (def ^:const t-spin 1) (def ^:const t-reachable 2)
(def ^:const t-touched 3) (def ^:const t-dropped 4)

(defrecord Handle [id token body])
(defrecord Source [id])
(defrecord Failure [error])
(defrecord CompactRuntime [gate nodes obligations events hosts work ready draining counters audit tokens])
(def w [:w 0])
(def root [:root w])
(def cancelled ::cancelled)

#?(:clj
   (defmacro locked [rt & body]
     (if (:ns &env) `(do ~@body) `(locking (:gate ~rt) ~@body))))

(defn runtime
  ([] (runtime {}))
  ([{:keys [audit?]}]
   (->CompactRuntime #?(:clj (Object.) :cljs nil) (id-dict) (dict) (queue) (queue) (queue)
                     #?(:clj (java.util.PriorityQueue.
                              11 (reify java.util.Comparator
                                   (compare [_ x y]
                                     (compare (long (a x n-rank)) (long (a y n-rank))))))
                        :cljs (array))
                     (atom false) (doto (slots 8) (put 0 0) (put 1 0) (put 2 0) (put 3 (id-dict)) (put 6 (members)) (put 7 (queue)))
                     (when audit? (atom [])) (when audit? (members)))))

(defn- next-number! [rt i]
  (put (:counters rt) i (inc (long (a (:counters rt) i)))))
(defn- current [node] (a node n-current))
(defn- open-owner? [owner] (or (identical? root owner) (and owner (not= :unwinding (a owner r-status)))))
(defn- mark! [rt node]
  (when (and node (not (a node n-work)))
    (put node n-work true) (push! (:work rt) node)))
(defn- reactive? [run]
  (boolean (and run (any! (a run r-obs) #(#{:track :await-reactive} (a % o-kind))))))
(declare wanted? retire! cancel! reclaim! snapshot schedule! adopt! collect-token!)

(defn- wanted? [node]
  (or (and (open-owner? (a node n-owner))
           (or (not= :spin (a node n-kind)) (not (a node n-complete)) (a node n-kept)))
      (any! (values (a node n-runs)) #(#{:running :parked :inherited :stale} (a % r-status)))
      (pos? (count! (a node n-dependents)))
      (any! (values (a node n-runs))
            (fn [run]
              (and (= :completed (a run r-status))
                   (or (pos? (count! (a run r-childruns)))
                       (any! (a run r-owned) #(and (not (identical? node %)) (wanted? %)))))))))

(defn- owner! [rt node owner]
  (let [old (a node n-owner)]
    (when-not (identical? old owner)
      (when (and old (not (identical? root old)))
        (remove! (a old r-owned) node) (mark! rt (a old r-node)))
      (put node n-owner owner)
      (when (and owner (not (identical? root owner)))
        (add! (a owner r-owned) node) (mark! rt (a owner r-node)))
      (mark! rt node))))

(defn- node! [rt id kind owner]
  (let [node (slots 20)]
    (put node n-id id) (put node n-kind kind) (put node n-complete false)
    (put node n-kept false) (put node n-tokens (members)) (put node n-order 0)
    (put node n-runs (dict)) (put node n-dependents (members))
    (put node n-generation (or (find! (a (:counters rt) 3) id) 0)) (put node n-rank 0)
    (assoc! (:nodes rt) id node) (owner! rt node owner) node))

(defn- end-ob! [rt ob]
  (when (a ob o-live)
    (put ob o-live false)
    (dissoc! (:obligations rt) (a ob o-id))
    (when-let [run (a ob o-run)] (remove! (a run r-obs) ob))
    (when-let [node (a ob o-debtor)]
      (remove! (a node n-dependents) ob) (mark! rt node))))

(defn- reject-dependent! [rt ob]
  (if-let [run (a ob o-run)]
    (when (and (= :armed (a ob o-slot)) (= :parked (a run r-status)))
      (put run r-status :running) (put ob o-value cancelled)
      (schedule! rt (a run r-node) ob))
    (push! (:hosts rt) (doto (slots 2) (put 0 ob) (put 1 cancelled))))
  (end-ob! rt ob))

(defn- release-owned! [rt run]
  (each-copy! [node (a run r-owned)]
              (owner! rt node nil)
              (when (= :spin (a node n-kind)) (put node n-dirty true))
              (each-copy! [child (values (a node n-runs))]
                          (if (#{:running :parked} (a child r-status)) (cancel! rt child) (retire! rt child)))
              (each-copy! [ob (a node n-dependents)] (reject-dependent! rt ob))))

(defn- forget-run! [rt run]
  (let [node (a run r-node)]
    (dissoc! (a node n-runs) (a run r-gen))
    (remove! (a (:counters rt) 6) run)
    (when (identical? run (current node))
      (put node n-current (last (sort-by #(a % r-gen) (values (a node n-runs)))))))
  (mark! rt (a run r-node)))

(defn- retire! [rt run]
  (when-not (= :unwinding (a run r-status))
    (let [physical? (a run r-physical)
          anchor (when physical?
                   (loop [owner run chain []]
                     (if (identical? root owner) (conj chain root w)
                         (recur (a owner r-owner) (conj chain [(a (a owner r-node) n-id) (a owner r-gen)])))))]
      (each-copy! [ob (a run r-obs)] (end-ob! rt ob))
      (each-copy! [child (a run r-childruns)] (cancel! rt child))
      (release-owned! rt run)
      (each! [owner (a run r-backlinks)] (remove! (a owner r-spawned) run))
      (each! [child (a run r-spawned)] (remove! (a child r-backlinks) run))
      (each! [node (a run r-created)]
             (when (identical? run (a node n-creator))
          ;; A surviving cache keeps the logical creator ID, not the old run's
          ;; mutable ownership graph.
               (put node n-creator [(a (a run r-node) n-id) (a run r-gen)])))
      (when-let [owner (a run r-owner)]
        (when-not (identical? root owner)
          (remove! (a owner r-childruns) run) (mark! rt (a owner r-node))))
      (if physical?
        (do (put run r-status :unwinding) (put run r-owner nil) (put run r-pred nil)
            (put run r-anchor anchor)
            #?(:clj (do (.clear ^java.util.Set (a run r-created)) (.clear ^java.util.Set (a run r-spawned)))
               :cljs (do (.clear (a run r-created)) (.clear (a run r-spawned)))))
        (forget-run! rt run))
      (mark! rt (a run r-node)))))

(defn- cancel! [rt run]
  (let [node (a run r-node) current? (identical? run (current node))]
    (retire! rt run)
    (when current?
      (each-copy! [ob (a node n-dependents)] (reject-dependent! rt ob)))
    (put node n-dirty true)))

(defn- reclaim! [rt]
  (loop []
    (when-let [node (pop! (:work rt))]
      (put node n-work false)
      (when (and (identical? node (find! (:nodes rt) (a node n-id))) (not (wanted? node)))
        (when (and (= :spin (a node n-kind)) (a node n-complete))
          (each-copy! [run (values (a node n-runs))] (retire! rt run))
          (owner! rt node nil))
        (when-not (and (= :spin (a node n-kind)) (a node n-complete)
                       (pos? (count! (a node n-tokens))))
          (each-copy! [run (values (a node n-runs))] (retire! rt run))
          (when-let [creator (a node n-creator)]
            (when-not (vector? creator) (remove! (a creator r-created) node)))
          (dissoc! (:nodes rt) (a node n-id))
          (put node n-body nil)))
      (recur))))

(defn- boundary! [rt action]
  (reclaim! rt)
  (when (:audit rt) (swap! (:audit rt) conj [action (snapshot rt)])))

(defn- touch! [node token]
  (when token (add! (a node n-tokens) token) (add! (a token t-touched) w)))
(defn- check-token! [token]
  (when (and token (has? (a token t-dropped) w))
    (throw (ex-info "Idle cache released" {:error :idle-cache-released}))))

(defn- check-running! [run]
  (when (and run (= :unwinding (a run r-status)))
    (throw (ex-info "Cancelled execution slice" {:error :cancelled}))))

(defn- predecessor-run? [previous caller]
  (when (and previous caller (not (identical? root previous)))
    (let [id (if (vector? previous) previous [(a (a previous r-node) n-id) (a previous r-gen)])
          node (a caller r-node)]
      (when (= (first id) (a node n-id))
        (loop [gen (a caller r-pred)]
          (cond (nil? gen) false
                (= gen (second id)) true
                :else (when-let [row (find! (a node n-runs) gen)] (recur (a row r-pred)))))))))

(defn signal [rt id value]
  (locked rt
          (let [run (when *activation* (a *activation* 1))
                order (if run (put *activation* 2 (inc (long (a *activation* 2)))) 0)
                _ (check-running! run)
                old (find! (:nodes rt) id)
                node (or old (node! rt id :signal (or run root)))]
            (when-not (= :signal (a node n-kind)) (throw (ex-info "Source ID collision" {:id id})))
            (when (or (nil? old) (predecessor-run? (a node n-owner) run))
              (when-not old (put node n-value value))
              (owner! rt node (or run root)) (put node n-order order)
              (when run (add! (a run r-created) node)))
            (boundary! rt (when (:audit rt) (cond-> {:t :t02 :w w :e id :value value}
                                              run (assoc :r [(a (a run r-node) n-id) (a run r-gen)] :order order))))
            (->Source id))))

#?(:clj (defonce ^:private handle-cleaner (java.lang.ref.Cleaner/create))
   :cljs (defonce ^:private handle-cleaner
           (js/FinalizationRegistry.
            (fn [held]
              (when-let [rt (.deref (aget held 0))]
                (collect-token! rt (aget held 1)))))))

(defn- arm-handle! [rt handle token]
  #?(:clj (let [runtime-ref (java.lang.ref.WeakReference. rt)]
            (put token 5 (.register ^java.lang.ref.Cleaner handle-cleaner handle
                                    (reify Runnable
                                      (run [_] (when-let [runtime (.get runtime-ref)]
                                                 (collect-token! runtime token)))))))
     :cljs (.register handle-cleaner handle (array (js/WeakRef. rt) token) token))
  handle)

(defn- collect-token! [rt token]
  (locked rt
          (when (a token t-reachable)
            (put token t-reachable false)
            (let [id (a token t-spin) node (find! (:nodes rt) id)]
              (when (and node (has? (a token t-touched) w))
                (push! (a (:counters rt) 7) token))
              (boundary! rt (when (:audit rt) {:t :t16 :tok (a token t-id)}))))
          (loop []
            (when-let [dead (pop! (a (:counters rt) 7))]
              (when-let [node (find! (:nodes rt) (a dead t-spin))]
                (remove! (a node n-tokens) dead) (mark! rt node))
              (boundary! rt (when (:audit rt) {:t :t17 :w w :e (a dead t-spin) :tok (a dead t-id)}))
              (recur)))))

(defn notify-unreachable!
  "Deterministic exercise of the host-finalization handoff for experiments."
  [rt handle]
  #?(:clj (.clean ^java.lang.ref.Cleaner$Cleanable (a (:token handle) 5))
     :cljs (do (.unregister handle-cleaner (:token handle)) (collect-token! rt (:token handle)))))

(defn make-spin [rt id body]
  (let [token (slots 6)]
    (put token t-id (random-uuid)) (put token t-spin id) (put token t-reachable true)
    (put token t-touched (members)) (put token t-dropped (members))
    (locked rt
            (when (:tokens rt) (add! (:tokens rt) token))
            (let [run (when *activation* (a *activation* 1))
                  order (if run (put *activation* 2 (inc (long (a *activation* 2)))) 0)
                  node (find! (:nodes rt) id)]
              (check-running! run)
              (when (and run (nil? node))
                (let [node (node! rt id :spin run)]
                  (put node n-creator run) (put node n-kept (reactive? run)) (put node n-order order)
                  (add! (a run r-created) node)))
              (when-let [node (find! (:nodes rt) id)]
                (when (predecessor-run? (a node n-creator) run)
                  (adopt! rt node run)
                  (owner! rt node run) (put node n-creator run) (put node n-kept (reactive? run))
                  (put node n-order order) (add! (a run r-created) node))
                (touch! node token))
              (boundary! rt (when (:audit rt) (cond-> {:t :t01 :w w :e id :tok (a token t-id)}
                                                run (assoc :r [(a (a run r-node) n-id) (a run r-gen)] :order order))))))
    (arm-handle! rt (->Handle id token body) token)))

(defn track [& _] (throw (ex-info "track requires cspin" {})))
(defn await [& _] (throw (ex-info "await requires cspin" {})))
#?(:clj
   (do
     (defn bp-track [_ r e] (fn [args] `(track-effect! ~@args ~r ~e)))
     (defn bp-await [_ r e] (fn [args] `(await-effect! ~@args ~r ~e)))
     (defmacro cspin [rt id & body]
       `(make-spin ~rt ~id ~(compiler/build-cps-fn
                             body (merge cps/breakpoints
                                         {'org.replikativ.spindel.compact-runtime/track
                                          'org.replikativ.spindel.compact-runtime/bp-track
                                          'org.replikativ.spindel.compact-runtime/await
                                          'org.replikativ.spindel.compact-runtime/bp-await}) &env)))))

(defn- schedule! [rt node ob]
  (put node n-pending-generation (a (current node) r-gen))
  (let [previous (a node n-resume)]
    (when (or (nil? previous) (and ob (< (long (a ob o-order)) (long (a previous o-order)))))
      (put node n-resume ob)))
  (when-not (a node n-ready)
    (put node n-ready true)
    #?(:clj (.add ^java.util.PriorityQueue (:ready rt) node)
       :cljs (.push (:ready rt) node))))

(defn- start! [rt node owner reentry?]
  (when-not reentry? (put node n-resume nil))
  (let [run (slots 14)
        pred (current node)
        generation (inc (long (a node n-generation)))]
    (put node n-generation generation)
    (assoc! (a (:counters rt) 3) (a node n-id) generation)
    (put run r-node node) (put run r-gen generation) (put run r-owner owner)
    (put run r-pred (when (and pred (not= :unwinding (a pred r-status))) (a pred r-gen))) (put run r-status :running)
    (put run r-created (members)) (put run r-spawned (members))
    (put run r-owned (members)) (put run r-obs (members))
    (put run r-backlinks (members)) (put run r-childruns (members))
    (put run r-seq (put (:counters rt) 1 (inc (max (long (a (:counters rt) 1)) (long (a (:counters rt) 2))))))
    (assoc! (a node n-runs) generation run)
    (add! (a (:counters rt) 6) run)
    (put node n-current run)
    (when-not (identical? root owner)
      (add! (a owner r-spawned) run) (add! (a run r-backlinks) owner)
      (add! (a owner r-childruns) run))
    (schedule! rt node nil)
    (mark! rt node) run))

(defn- ob! [rt kind debtor run order resolve reject]
  (let [ob (slots 14) id (a (:counters rt) 0)]
    (next-number! rt 0)
    (put ob o-id id) (put ob o-kind kind) (put ob o-debtor debtor) (put ob o-run run)
    (put ob o-standing (boolean (#{:track :await-reactive :callback} kind)))
    (put ob o-resolve resolve) (put ob o-reject reject) (put ob o-order order)
    (put ob o-slot (if (= kind :track) :consumed :armed)) (put ob o-live true)
    (assoc! (:obligations rt) id ob)
    (when run (add! (a run r-obs) ob))
    (add! (a debtor n-dependents) ob) (mark! rt debtor) ob))

(defn- adopt! [rt node caller]
  (let [previous (a node n-owner)]
    (when (predecessor-run? previous caller)
      (when (identical? previous (a node n-creator))
        (put node n-creator caller) (put node n-kept (reactive? caller))
        (add! (a caller r-created) node))
      (owner! rt node caller)
      (each! [run (values (a node n-runs))]
             (when (identical? previous (a run r-owner))
               (remove! (a previous r-childruns) run) (put run r-owner caller) (add! (a caller r-childruns) run))))))

(defn- rank! [run debtor]
  (let [node (a run r-node)]
    (put node n-rank (max (long (a node n-rank)) (inc (long (a debtor n-rank)))))))

(defn track-effect! [source resolve reject]
  (let [rt (a *activation* 0) run (a *activation* 1)
        order (put *activation* 2 (inc (long (a *activation* 2))))
        value (locked rt
                      (check-running! run)
                      (let [node (find! (:nodes rt) (:id source))
                            ob (ob! rt :track node run order resolve reject)]
                        (put ob o-last (a node n-value)) (rank! run node)
                        (boundary! rt (when (:audit rt) {:t :t05 :w w :r [(a (a run r-node) n-id) (a run r-gen)]
                                                         :kind :track :order order :debtor [:entity w (:id source)]}))
                        (a node n-value)))]
    (cps/invoke-continuation resolve (iv/->Interval value value nil))))

(defn- deliver-cont! [ob value]
  (cond
    (= cancelled value) (cps/invoke-continuation (a ob o-reject) (ex-info "Cancelled" {:error :cancelled}))
    (instance? Failure value) (cps/invoke-continuation (a ob o-reject) (:error value))
    :else (cps/invoke-continuation (a ob o-resolve) value)))

(defn await-effect! [source resolve reject]
  (let [rt (a *activation* 0) run (a *activation* 1)
        order (put *activation* 2 (inc (long (a *activation* 2))))
        ob (locked rt
                   (check-running! run)
                   (check-token! (:token source))
                   (let [node (or (find! (:nodes rt) (:id source)) (node! rt (:id source) :spin run))]
                     (put node n-body (:body source))
                     (adopt! rt node run)
                     (when (and (not (a node n-complete)) (nil? (current node))) (start! rt node run false))
                     (let [ob (ob! rt :await-reactive node run order resolve reject)]
                       (put run r-status :parked) (touch! node (:token source)) (rank! run node)
                       (boundary! rt (when (:audit rt) (cond-> {:t :t05 :w w :r [(a (a run r-node) n-id) (a run r-gen)]
                                                                :kind :await-reactive
                                                                :order order :debtor [:entity w (:id source)]}
                                                         (:token source) (assoc :tok (a (:token source) t-id)))))
                       (when (and (a node n-complete)
                                  (not (#{:running :parked} (some-> (current node) (a r-status)))))
                         (put ob o-slot :consumed) (put run r-status :running)
                         (put ob o-value (a node n-value))
                         (boundary! rt (when (:audit rt) {:t :t06 :w w :o [:o (a ob o-id)] :value (a node n-value)})))
                       ob)))]
    (when (= :consumed (a ob o-slot)) (deliver-cont! ob (a ob o-value)))))

(defn- complete! [rt run value]
  (locked rt
          (let [node (a run r-node)]
            (when (and (identical? run (current node)) (= :running (a run r-status)))
              (put node n-complete true) (put node n-dirty false) (put node n-value value)
              (put run r-status :completed)
              (push! (:events rt) (doto (slots 3) (put 0 node) (put 1 value) (put 2 (put (:counters rt) 2 (inc (max (long (a (:counters rt) 1)) (long (a (:counters rt) 2))))))))
              (each-copy! [previous (values (a node n-runs))]
                          (when (and (not (identical? previous run)) (#{:completed :stale} (a previous r-status)))
                            (retire! rt previous)))
              (mark! rt node))
            (boundary! rt (when (:audit rt) {:t :t07 :w w :r [(a node n-id) (a run r-gen)] :value value})))))

(defn- reenter! [rt node trigger]
  (let [previous (current node) work? (#{:running :parked} (a previous r-status))
        order (a trigger o-order)]
    (each-copy! [old (values (a node n-runs))]
                (when (= :stale (a old r-status)) (retire! rt old)))
    (let [run (start! rt node (a previous r-owner) true)]
      (when work?
        (put previous r-status :stale)
        (each-copy! [ob (a previous r-obs)]
                    (if (and (= :track (a ob o-kind)) (<= (long (a ob o-order)) (long order)))
                      (do (remove! (a previous r-obs) ob) (put ob o-run run) (add! (a run r-obs) ob))
                      (end-ob! rt ob))))
      (each-copy! [child (a previous r-created)]
                  (when (< (long (a child n-order)) (long order))
                    (owner! rt child run)
                    (when (a child n-creator) (put child n-creator run))
                    (remove! (a previous r-created) child) (add! (a run r-created) child)
                    (each! [cr (values (a child n-runs))]
                           (when (identical? previous (a cr r-owner))
                             (remove! (a previous r-childruns) cr) (put cr r-owner run) (add! (a run r-childruns) cr)))))
      (schedule! rt node trigger))))

(defn- process-event! [rt event]
  (let [node (a event 0) value (a event 1)
        dependents (copy-items (a node n-dependents))]
    (dotimes [index (alength ^objects dependents)]
      (let [ob (a dependents index)]
        (if-let [run (a ob o-run)]
          (if (= :consumed (a ob o-slot))
            (reenter! rt (a run r-node) ob)
            (when (= :parked (a run r-status))
              (put ob o-slot :consumed) (put ob o-value value) (put run r-status :running)
              (schedule! rt (a run r-node) ob)))
          (do (push! (:hosts rt) (doto (slots 2) (put 0 ob) (put 1 value)))
              (when (and (a node n-complete) (not (reactive? (current node)))) (end-ob! rt ob))))))
    (boundary! rt (when (:audit rt) {:t :t08 :w w :e (a node n-id) :value value
                                     :delivery-order (mapv #(vector :o (a % o-id)) dependents)}))))

(defn- poll-ready! [rt]
  #?(:clj (.poll ^java.util.PriorityQueue (:ready rt))
     :cljs (when (pos? (.-length (:ready rt)))
             (.sort (:ready rt) (fn [x y] (- (a x n-rank) (a y n-rank))))
             (.shift (:ready rt)))))

(declare drain!)
(defn- finish-slice! [rt run]
  (locked rt
          (put run r-physical false)
          (put (:counters rt) 4 nil)
          (when (= :unwinding (a run r-status)) (forget-run! rt run))
          (boundary! rt (when (:audit rt) {:t :t38 :th :engine}))))

(defn- execute! [rt node]
  (when-let [activation
             (locked rt
                     (let [run (current node) ob (a node n-resume)]
                       (put node n-ready false) (put node n-resume nil)
                       (when (and run (= :running (a run r-status))
                                  (= (a run r-gen) (a node n-pending-generation)))
                         (when ob (rank! run (a ob o-debtor)))
                         (put run r-physical true)
                         (put (:counters rt) 4 run) (put (:counters rt) 5 true)
                         (boundary! rt (when (:audit rt) {:t :slice-enter :w w :r [(a node n-id) (a run r-gen)] :th :engine}))
                         (doto (slots 7) (put 0 rt) (put 1 run)
                               (put 2 (if ob (a ob o-order) -1)) (put 3 ob) (put 4 (a node n-body))
                               (put 5 (when ob (a (a ob o-debtor) n-value)))
                               (put 6 (when ob (a (a ob o-debtor) n-body)))))))]
    (let [run (a activation 1) ob (a activation 3)]
      (try
        (binding [*activation* activation cps/*in-trampoline* false]
          (if ob
            (if (= :track (a ob o-kind))
              (if (identical? run (a ob o-run))
                (cps/invoke-continuation (a ob o-resolve) (iv/->Interval (a ob o-last) (a activation 5) nil))
                (do (put activation 2 (dec (long (a ob o-order))))
                    (track-effect! (->Source (a (a ob o-debtor) n-id)) (a ob o-resolve) (a ob o-reject))))
              (if (identical? run (a ob o-run))
                (deliver-cont! ob (a ob o-value))
                (do (put activation 2 (dec (long (a ob o-order))))
                    (await-effect! (->Handle (a (a ob o-debtor) n-id) nil (a activation 6))
                                   (a ob o-resolve) (a ob o-reject)))))
            ((a activation 4)
             (fn [value] (complete! rt (a *activation* 1) value))
             (fn [error] (complete! rt (a *activation* 1) (->Failure error))))))
        (finally (finish-slice! rt run))))))

(defn drain! [rt]
  (when (compare-and-set! (:draining rt) false true)
    (try
      (loop []
        (let [entry (locked rt
                            (if-let [event (pop! (:events rt))]
                              (do (process-event! rt event) :event)
                              (or (poll-ready! rt) (pop! (:hosts rt)))))]
          (when entry
            (when-not (= :event entry)
              (if (= 2 (alength ^objects entry))
                (let [ob (a entry 0) value (a entry 1)]
                  (cond
                    (instance? Failure value) ((a ob o-failure) (:error value))
                    (= cancelled value) ((a ob o-failure) (ex-info "Cancelled" {}))
                    :else ((a ob o-success) value)))
                (execute! rt entry)))
            (recur))))
      (finally (reset! (:draining rt) false)))
    (when (locked rt (or (queued? (:events rt)) (queued? (:hosts rt))
                         #?(:clj (not (.isEmpty ^java.util.PriorityQueue (:ready rt)))
                            :cljs (pos? (.-length (:ready rt))))))
      (drain! rt))))

(defn observe! [rt handle success failure]
  (let [ob (locked rt
                   (check-token! (:token handle))
                   (let [node (or (find! (:nodes rt) (:id handle)) (node! rt (:id handle) :spin root))
                         cached? (and (a node n-complete) (not (a node n-dirty)) (not (#{:running :parked} (some-> (current node) (a r-status)))))]
                     (put node n-body (:body handle))
                     (when-not (a node n-owner) (owner! rt node root))
                     (touch! node (:token handle))
                     (when-not (or cached? (#{:running :parked} (some-> (current node) (a r-status)))) (start! rt node root false))
                     (let [ob (ob! rt :callback node nil 0 nil nil)]
                       (put ob o-success success) (put ob o-failure failure)
                       (when cached?
                         (push! (:hosts rt) (doto (slots 2) (put 0 ob) (put 1 (a node n-value))))
                         (when-not (reactive? (current node)) (end-ob! rt ob)))
                       (boundary! rt (when (:audit rt) {:t :t04 :w w :e (:id handle) :tok (a (:token handle) t-id) :mode :callback}))
                       ob)))]
    (drain! rt)
    (fn []
      (locked rt
              (end-ob! rt ob)
              (boundary! rt (when (:audit rt) {:t :unsubscribe :w w :o [:o (a ob o-id)]})))
      (drain! rt))))

(defn set-signal! [rt source value]
  (locked rt
          (let [node (find! (:nodes rt) (:id source))]
            (when-not (and node (a node n-owner)) (throw (ex-info "Released source" {:id (:id source)})))
            (put node n-value value)
            (push! (:events rt) (doto (slots 3) (put 0 node) (put 1 value) (put 2 (put (:counters rt) 2 (inc (max (long (a (:counters rt) 1)) (long (a (:counters rt) 2))))))))
            (boundary! rt (when (:audit rt) {:t :signal-write :w w :e (:id source) :value value}))))
  (drain! rt))

(defn cancel-spin! [rt handle]
  (locked rt
          (let [node (find! (:nodes rt) (:id handle)) run (when node (current node))]
            (when run (cancel! rt run))
            (boundary! rt (when (:audit rt) {:t :t11 :w w :r (when run [(a node n-id) (a run r-gen)])}))))
  (drain! rt))

(defn release-idle! [rt]
  (locked rt
          (doseq [node (vec (values (:nodes rt)))
                  :when (and (= :spin (a node n-kind)) (a node n-complete) (not (wanted? node)))]
            (doseq [token (items (a node n-tokens))] (add! (a token t-dropped) w))
            #?(:clj (.clear ^java.util.Set (a node n-tokens)) :cljs (.clear (a node n-tokens)))
            (mark! rt node))
          (boundary! rt (when (:audit rt) {:t :t18 :w w}))))

(defn- run-id [run]
  (when run (if (vector? run) run [(a (a run r-node) n-id) (a run r-gen)])))
(defn- owner-id [owner] (if (identical? root owner) root (run-id owner)))
(defn snapshot [rt]
  (locked rt
          {:entities (into {} (for [node (values (:nodes rt))]
                                [(a node n-id)
                                 (cond-> {:kind (a node n-kind) :origin :created :owner (owner-id (a node n-owner))
                                          :creator (run-id (a node n-creator)) :completed? (boolean (a node n-complete))
                                          :kept? (boolean (a node n-kept)) :result (a node n-value)
                                          :tokens (set (map #(a % t-id) (items (a node n-tokens)))) :key nil :order (a node n-order)}
                                   (some? (a node n-dirty)) (assoc :dirty? (a node n-dirty)))]))
           :runs (into {} (for [run (items (a (:counters rt) 6)) :let [node (a run r-node)]]
                            [(run-id run) (cond-> {:spin (a node n-id) :owner (owner-id (a run r-owner))
                                                   :pred (when-let [gen (a run r-pred)] [(a node n-id) gen])
                                                   :status (a run r-status) :seq (a run r-seq)
                                                   :creations (set (map #(a % n-id) (items (a run r-created))))
                                                   :spawned (set (map run-id (items (a run r-spawned))))}
                                            (= :unwinding (a run r-status)) (assoc :retired? true :anchor (a run r-anchor)))]))
           :obligations (into {} (for [ob (values (:obligations rt))]
                                   [[:o (a ob o-id)]
                                    (cond-> {:kind (a ob o-kind) :debtor [:entity w (a (a ob o-debtor) n-id)]
                                             :creditor (if-let [run (a ob o-run)] [:run w (run-id run)] [:host :caller])
                                             :standing? (a ob o-standing) :cont (when (a ob o-run) [:continuation [:o (a ob o-id)]])
                                             :token nil :order (a ob o-order) :slot (a ob o-slot)}
                                      (a ob o-run) (assoc :origin :created)
                                      (nil? (a ob o-run)) (assoc :filter {:mode :local :origin w}))]))
           :queue (mapv (fn [event] {:completion (a (a event 0) n-id) :debtor-world w :value (a event 1) :seq (a event 2)})
                        #?(:clj (seq (:events rt)) :cljs (array-seq (:events rt))))
           :seq (a (:counters rt) 1)
           :serial (a (:counters rt) 0) :clock (a (:counters rt) 2)
           :threads (let [run (a (:counters rt) 4)]
                      (cond-> {:host {:world w :scope nil :run nil :read-permits #{} :excl-permits []}}
                        (a (:counters rt) 5)
                        (assoc :engine (cond-> {:world w :scope (run-id run) :run (run-id run) :executing? (boolean run)}
                                         run (assoc :obligation-world w)
                                         (= :unwinding (some-> run (a r-status))) (assoc :retired? true)))))
           :gc (mapv (fn [token] {:t :t17 :w w :e (a token t-spin) :tok (a token t-id)})
                     #?(:clj (seq (a (:counters rt) 7)) :cljs (array-seq (a (:counters rt) 7))))
           :handles (when (:tokens rt)
                      (into {} (for [token (items (:tokens rt))]
                                 [(a token t-id) {:spin (a token t-spin) :reachable? (a token t-reachable)
                                                  :touched (set (items (a token t-touched))) :dropped (set (items (a token t-dropped)))}])))}))
