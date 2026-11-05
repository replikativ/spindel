(ns org.replikativ.spindel.v2.lifetime-test
  "Controlled collection/dispatch fixtures: no dependence on host GC timing."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.lifetime :as lt]))

(defn- controlled [f]
  (let [refs (atom []) cleaners (atom []) queue (atom clojure.lang.PersistentQueue/EMPTY)
        weak hs/weak
        collect! (fn [target]
                   (let [actions (vec (keep (fn [[r action]] (when (identical? target (hs/deref-weak r)) action)) @cleaners))]
                     (doseq [^java.lang.ref.WeakReference r @refs]
                       (when (identical? target (.get r)) (.clear r)))
                     (doseq [action actions] (action))))
        step! (fn [] (when-let [f (peek @queue)] (swap! queue pop) (f) true))
        drain! (fn [] (loop [n 0]
                        (when (step!)
                          (when (> n 100) (throw (ex-info "maintenance did not quiesce" {})))
                          (recur (inc n)))))
        enqueue! (fn ([f] (swap! queue conj f) nil)
                   ([f _] (swap! queue conj f) nil))]
    (with-redefs [hs/weak (fn [x] (let [r (weak x)] (swap! refs conj r) r))
                  hs/on-collect! (fn [x action] (swap! cleaners conj [(hs/weak x) action]) nil)
                  hs/metadata-later! enqueue!]
      (f {:collect! collect! :step! step! :drain! drain! :queue queue :cleaners cleaners}))))

(deftest collection-sweeps-every-idle-world-with-coalesced-requests
  (controlled
   (fn [{:keys [collect! drain! queue]}]
     (let [p (v2/world) a (binding [v2/*world* p] (v2/atom :a))
           b (binding [v2/*world* p] (v2/atom :b))
           c (v2/fork! p) d (v2/fork! p)]
       (collect! a)
       (is (= 3 (count @queue)))
       (collect! b)
       (is (= 3 (count @queue)) "one pending pass per world")
       (drain!)
       (doseq [w [p c d]]
         (is (empty? (aget ^objects w rw/W-ATOMS)))
         (is (false? (hs/flag? (aget ^objects w rw/W-SWEEP-PENDING))))
         (is (= 2 (aget ^objects w rw/W-SWEEP-GEN))))))))

(deftest maintenance-does-not-activate-dormant-or-unborn-work
  (controlled
   (fn [{:keys [collect! drain!]}]
     (let [p (v2/world)
           a (binding [v2/*world* p] (v2/atom :dead))
           t (binding [v2/*world* p] (task (v2/sleep 60000) :later))
           c (v2/fork! p) unborn (v2/fork! p)
           dormant (aget ^objects c rw/W-DORMANT)
           ready (vec (aget ^objects c rw/W-START))]
       (aset ^objects unborn rw/W-UNBORN true)
       (collect! a) (drain!)
       (is (identical? dormant (aget ^objects c rw/W-DORMANT)))
       (is (= ready (vec (aget ^objects c rw/W-START))))
       (is (true? (aget ^objects unborn rw/W-UNBORN)))
       (is (empty? (aget ^objects unborn rw/W-ATOMS)))
       (v2/release-world! unborn)
       (v2/release-world! c)
       (v2/cancel-task! t)
       (v2/release-world! p)))))

(deftest busy-gate-does-not-lose-maintenance
  (controlled
   (fn [{:keys [collect! step! drain! queue]}]
     (let [w (v2/world) a (binding [v2/*world* w] (v2/atom 1))
           held (promise) release (promise)
           worker (future (let [lk (aget ^objects w rw/W-LOCK)]
                            (hs/try-lock! lk) (deliver held true)
                            @release (hs/unlock! lk)))]
       (is (= true (deref held 2000 false)))
       (collect! a) (step!)
       (is (= 1 (count @queue)))
       (is (true? (hs/flag? (aget ^objects w rw/W-SWEEP-PENDING))))
       (deliver release true) @worker
       (drain!)
       (is (empty? (aget ^objects w rw/W-ATOMS)))))))

(deftest a-fork-registering-after-collection-cannot-miss-the-sweep
  (controlled
   (fn [{:keys [collect! drain!]}]
     (let [p (v2/world) a (binding [v2/*world* p] (v2/atom 1))
           register lt/register-world!
           c (with-redefs [lt/register-world! (fn [family w id idx generation request!]
                                                (collect! a)
                                                (register family w id idx generation request!))]
               (v2/fork! p))]
       (drain!)
       (is (empty? (aget ^objects c rw/W-ATOMS)))
       (is (= 1 (aget ^objects c rw/W-SWEEP-GEN)))))))

(deftest collection-during-a-scan-queues-the-next-generation
  (controlled
   (fn [{:keys [collect! drain! queue step!]}]
     (let [w (v2/world) a (binding [v2/*world* w] (v2/atom :a))
           b (binding [v2/*world* w] (v2/atom :b))
           ref (first (get (aget ^objects w rw/W-ATOMS) (.-id ^org.replikativ.spindel.v2.core.RAtom b)))
           deref-weak hs/deref-weak fired? (atom false)]
       (collect! a)
       (with-redefs [hs/deref-weak (fn [r]
                                     (when (and (identical? ref r) (compare-and-set! fired? false true))
                                       (collect! b))
                                     (deref-weak r))]
         (step!))
       (is @fired?)
       (is (= 1 (count @queue)))
       (drain!)
       (is (= 2 (aget ^objects w rw/W-SWEEP-GEN)))
       (is (empty? (aget ^objects w rw/W-ATOMS)))))))

(deftest aliases-share-home-watches-without-owner-membership-history
  (controlled
   (fn [_]
     (doseq [verify? [false true]]
       (let [w (v2/world {:verify? verify?}) s (binding [v2/*world* w] (v2/signal 0))
             alias (v2/in-world w s) seen (atom [])
             token (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle s) 1)]
         (add-watch s :k (fn [k _ o n] (swap! seen conj [k o n])))
         (dotimes [_ 100]
           (let [h (v2/resolve-ref w (v2/world-ref s))]
             (is (identical? token (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle h) 1)))))
         (is (= 0 (hs/msize (:owners token))))
         (reset! alias 1)
         (is (= [[:k 0 1]] @seen))
         (remove-watch alias :k)
         (is (empty? (.getWatches ^clojure.lang.IRef s)))
         (v2/release-world! w))))))

(deftest foreign-slice-watches-are-owned-by-the-invoking-handle
  (controlled
   (fn [{:keys [collect!]}]
     (let [p (v2/world) s (binding [v2/*world* p] (v2/signal 0))
           c (v2/fork! p) seen (atom [])
           t (binding [v2/*world* c]
               (task (add-watch s :foreign (fn [_ _ o n] (swap! seen conj [o n])))
                     (reset! s 1)))
           o (:foreign-owner (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle s) 2))]
       (is (= 1 (v2/value t)))
       (is (= [[0 1]] @seen))
       (is (= 1 (hs/msize (:capsules o))))
       (is (empty? (.getWatches ^clojure.lang.IRef s)) "parent callbacks are independent")
       (collect! c)
       (is (= 0 (hs/msize (:capsules o))))
       (is (= 0 (hs/msize (:weak-capsules o))))
       (reset! s 2)
       (is (= [[0 1]] @seen))))))

(deftest world-cleanup-detaches-live-atoms-and-delayed-capsule-cleaners-are-exact
  (controlled
   (fn [{:keys [collect! cleaners]}]
     (let [p (v2/world) a (binding [v2/*world* p] (v2/atom 1)) c (v2/fork! p)
           o (.-watch-owner ^org.replikativ.spindel.v2.core.RAtom a)]
       (binding [v2/*world* c] (add-watch a :k (fn [& _])))
       (is (= 1 (hs/msize (:capsules o))))
       (collect! c)
       (is (= 0 (hs/msize (:capsules o))))
       (binding [v2/*world* p] (is (= 1 @a))))
     (let [idx (lt/index) cell (object-array 3) old (lt/source-token! idx 1 cell)
           action (some (fn [[r f]] (when (identical? old (hs/deref-weak r)) f)) @cleaners)]
       (.clear ^java.lang.ref.WeakReference (hs/mget idx 1))
       (let [replacement (lt/source-token! idx 1 (object-array 3))]
         (action)
         (is (identical? replacement (hs/deref-weak (hs/mget idx 1)))))))))

(deftest atom-state-survives-release-until-finalizers-join
  (controlled
   (fn [_]
     (let [w (v2/world) a (binding [v2/*world* w] (v2/atom 0))
           entered (promise) finish (promise)
           t (binding [v2/*world* w]
               (task (try
                       (v2/offload #(do (deliver entered true)
                                        (loop []
                                          (when-not (realized? finish)
                                            (try (Thread/sleep 5) (catch InterruptedException _))
                                            (recur)))))
                       (finally (swap! a inc)))))]
       (is (= true (deref entered 2000 false)))
       (v2/release-world! w)
       (is (= 1 (count (aget ^objects w rw/W-ATOMS))))
       (deliver finish true)
       (loop [n 0]
         (when (and (< n 500) (not (aget ^objects w rw/W-META-CLOSED)))
           (Thread/sleep 5) (recur (inc n))))
       (is (true? (aget ^objects w rw/W-META-CLOSED)))
       (is (empty? (aget ^objects w rw/W-ATOMS)))
       (is (zero? (hs/msize (:worlds (aget ^objects w rw/W-FAMILY)))))
       (hs/fence! t)))))

(deftest ordinary-handles-allocate-no-watch-tokens-or-cleaners
  (controlled
   (fn [{:keys [cleaners]}]
     (let [w (v2/world) before (count @cleaners)]
       (binding [v2/*world* w]
         (let [t (task :task) c (v2/spin :comp) d (v2/deferred)]
           (doseq [h [t c d]]
             (is (nil? (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle h) 1))))
           (is (= before (count @cleaners)))
           (is (= 0 (hs/msize (aget ^objects w rw/W-WATCHES))))
           (let [s (v2/signal 0) n (count @cleaners)]
             (is (= (inc before) n) "one source capsule collection action")
             (dotimes [_ 20] (v2/in-world w s))
             (is (= n (count @cleaners)) "aliases share their home token"))))))))

(deftest collected-foreign-alias-owners-leave-no-membership-history
  (controlled
   (fn [{:keys [collect!]}]
     (let [p (v2/world) s (binding [v2/*world* p] (v2/signal 0))
           c (v2/fork! p)]
       (dotimes [_ 100]
         (let [h (v2/in-world p s)
               t (binding [v2/*world* c] (task (add-watch h :k (fn [& _]))))
               o (:foreign-owner (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle h) 2))
               cap (hs/mget (:capsules o) (aget ^objects c rw/ID))]
           (is (some? (v2/value t)))
           (is (= 1 (hs/msize (:owners cap))))
           (collect! o)
           (is (= 0 (hs/msize (:owners cap))))))
       (v2/release-world! c) (v2/release-world! p)))))

(deftest source-token-collection-cannot-run-a-forks-dormant-work-or-hook
  (controlled
   (fn [{:keys [collect! drain!]}]
     (let [hooks (atom 0) p (v2/world {:verify? true :hook (fn [& _] (swap! hooks inc))})
           s (binding [v2/*world* p] (v2/signal 0))
           t (binding [v2/*world* p] (task (v2/sleep 60000)))
           c (v2/fork! p)
           alias (v2/in-world c s)
           token (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle alias) 1)
           dormant (aget ^objects c rw/W-DORMANT)
           before @hooks]
       (collect! token) (drain!)
       (is (= before @hooks))
       (is (identical? dormant (aget ^objects c rw/W-DORMANT)))
       (is (empty? (aget ^objects c rw/W-ARMED)))
       (v2/release-world! c) (v2/cancel-task! t) (v2/release-world! p)))))

(deftest world-refs-carry-only-row-binding-not-watch-ownership
  (controlled
   (fn [_]
     (let [w (v2/world) h (binding [v2/*world* w] (v2/signal 1))
           r (v2/world-ref h)]
       (is (= 1 (alength ^objects (.-cell ^org.replikativ.spindel.v2.core.Ref r))))
       (is (instance? java.lang.ref.WeakReference
                      (aget ^objects (v2/row-of h) rw/HREF)))
       (v2/release-world! w)))))

(deftest pending-world-ref-receives-the-bound-row-without-owning-the-wrapper
  (controlled
   (fn [_]
     (let [queued (atom clojure.lang.PersistentQueue/EMPTY)
           executor (reify java.util.concurrent.Executor
                      (execute [_ f] (swap! queued conj f)))
           w (v2/world {:inline? false :executor executor})
           h (binding [v2/*world* w] (v2/signal :value))
           r (v2/world-ref h)]
       (is (nil? (v2/row-of h)))
       (loop []
         (when-let [^Runnable f (peek @queued)]
           (swap! queued pop) (.run f) (recur)))
       (let [alias (v2/resolve-ref w r)]
         (is (identical? (v2/row-of h) (v2/row-of alias)))
         (is (= :value (aget ^objects (v2/row-of alias) rw/X-VALUE))))
       (v2/release-world! w)
       (loop []
         (when-let [^Runnable f (peek @queued)]
           (swap! queued pop) (.run f) (recur)))))))

(deftest source-alias-recreation-keeps-one-logical-allowance
  (controlled
   (fn [{:keys [collect! drain!]}]
     (let [w (v2/world {:verify? true})
           original (binding [v2/*world* w] (v2/signal 0))
           alias (v2/in-world w original)
           row (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle original) 0)
           token (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle alias) 1)]
       (collect! original)
       (let [replacement (#'v2/host-call! w #(#'v2/handle! w row))]
         (is (= 1 (aget ^objects row rw/HANDLES)))
         (is (identical? token (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle replacement) 1))))
       (collect! token) (drain!)
       (is (zero? (aget ^objects row rw/HANDLES)))
       (is (nil? (hs/mget (aget ^objects w rw/W-REG) (aget ^objects row rw/ID))))))))

(deftest delayed-source-cleaner-cannot-drop-replacement-allowance
  (controlled
   (fn [{:keys [collect! drain!]}]
     (let [w (v2/world {:verify? true})
           original (binding [v2/*world* w] (v2/signal 0))
           row (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle original) 0)
           token (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle original) 1)]
       (collect! token)
       (let [alias (v2/in-world w original)
             replacement (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle alias) 1)]
         (drain!)
         (is (= 1 (aget ^objects row rw/HANDLES)))
         (v2/release! alias)
         (is (zero? (aget ^objects row rw/HANDLES)))
         (collect! original)
         (#'v2/host-call! w #(#'v2/handle! w row))
         (is (= 1 (aget ^objects row rw/HANDLES)))
         (collect! replacement) (drain!)
         (is (zero? (aget ^objects row rw/HANDLES))))))))

(deftest source-alias-after-collection-remains-a-nonowning-view
  (controlled
   (fn [{:keys [collect! drain!]}]
     (let [w (v2/world {:verify? true})
           original (binding [v2/*world* w] (v2/signal :value))
           ref (v2/world-ref original)
           row (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle original) 0)
           token (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle original) 1)]
       (collect! token) (drain!)
       ;; Resolving a Ref has never acquired an owning row handle. It is a
       ;; direct view, and retains its row and world-local watch token itself.
       (let [alias (v2/resolve-ref w ref)]
         (is (zero? (aget ^objects row rw/HANDLES)))
         (is (= :value (v2/value alias)))
         (add-watch alias :k (fn [& _]))
         (is (= #{:k} (set (keys (.getWatches ^clojure.lang.IRef alias))))))))))
