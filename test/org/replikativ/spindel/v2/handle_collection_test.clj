(ns org.replikativ.spindel.v2.handle-collection-test
  "Actual Cleaner-action injection, independent of host GC timing. Target
   aliases are lifecycle injections and are never used after their callback."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task]]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.v2.combinators :as comb]))

(defn- capture-handle [w make-handle]
  (let [register hs/on-collect! actions (atom []) thread (Thread/currentThread)
        h (with-redefs [hs/on-collect!
                        (fn [x action]
                          (if (and (instance? org.replikativ.spindel.v2.core.Handle x)
                                   (identical? w (.-w ^org.replikativ.spindel.v2.core.Handle x))
                                   (identical? thread (Thread/currentThread)))
                            (swap! actions conj [(hs/weak x) action])
                            (register x action)))]
            (make-handle))
        matches (filter #(identical? h (hs/deref-weak (first %))) @actions)]
    (assert (= 1 (count matches) (count @actions)))
    [h (second (first matches))]))

(defn- raw-row [w id] (hs/mget (aget ^objects w rw/W-REG) id))
(defn- row-id [h]
  (aget ^objects (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle h) 0) rw/ID))
(defn- snapshot [^objects row]
  (when row
    {:id (aget row rw/ID) :type (aget row rw/TYPE)
     :handles (aget row rw/HANDLES) :refs (aget row rw/REFS)
     :epoch (System/identityHashCode (aget row (dec (alength row))))
     :idle (when (= rw/T-COMP (aget row rw/TYPE)) (aget row rw/C-IDLE))}))
(defn- checkpoint! [w]
  (v2/assoc-in-world! w [:collection-checkpoint] true))
(defn- make-handle [w kind]
  (binding [v2/*world* w]
    (case kind
      :comp (spin :kept)
      :task (task :kept)
      :deferred (let [d (v2/deferred)] (v2/deliver! d :kept) d))))

(deftest collection-drops-only-the-owning-worlds-canonical-row
  (doseq [kind [:comp :task :deferred]
          origin [:child :parent]
          [copy-parent? copy-child?] [[false false] [false true] [true false] [true true]]]
    (testing (str [kind origin copy-parent? copy-child?])
      (let [divergences (atom [])
            p (v2/world {:verify? true :hook (verify/checking-hook divergences)})
            [h parent-action] (if (= origin :parent)
                                (capture-handle p #(make-handle p kind))
                                [(make-handle p kind) nil])
            _ (is (= :kept (v2/value h)))
            id (row-id h) basis (raw-row p id)
            c (v2/fork! p) sibling (v2/fork! p)
            [ch child-action] (if (= origin :child)
                                (capture-handle c #(v2/in-world c h))
                                [(v2/in-world c h) nil])
            sh (v2/in-world sibling h)
            target (if (= origin :child) c p)
            protected (if (= origin :child) [p sibling] [c sibling])
            action (or parent-action child-action)]
        (try
          (when copy-parent? (is (= :kept (v2/value h))))
          (when copy-child? (is (= :kept (v2/value ch))))
          (when (and copy-parent? copy-child?) (is (= :kept (v2/value sh))))
          ;; Observe raw registry entries: observation must not force COW.
          (is (= (not copy-parent?) (identical? basis (raw-row p id))))
          (is (= (not copy-child?) (identical? basis (raw-row c id))))
          (is (= (not (and copy-parent? copy-child?)) (identical? basis (raw-row sibling id))))
          (is (= 1 (:handles (snapshot (raw-row target id)))))
          (is (zero? (:refs (snapshot (raw-row target id)))))
          (let [before (mapv #(snapshot (raw-row % id)) protected)
                rows-before (mapv #(raw-row % id) protected)]
            (action)
            ;; Inline, free gate: the actual host ingress committed synchronously.
            (is (nil? (raw-row target id)) "the dropped, unreferenced row retires")
            (is (= before (mapv #(snapshot (raw-row % id)) protected)))
            (is (every? true? (map identical? rows-before (map #(raw-row % id) protected))))
            (doseq [w protected] (checkpoint! w))
            (is (empty? @divergences) (str @divergences))
            (let [log-size (count (aget ^objects target rw/W-LOG))]
              (action)
              (is (= log-size (count (aget ^objects target rw/W-LOG))) "drop is idempotent")))
          ;; Only unaffected handles are used after the injected event.
          (doseq [kept (if (= origin :child) [h sh] [ch sh])]
            (is (= :kept (v2/value kept)))
            (hs/fence! kept))
          (finally
            (hs/fence! [h ch sh])
            (doseq [w [c sibling p]] (v2/release-world! w))))))))

(deftest collection-preserves-a-row-with-an-engine-reason
  (doseq [kind [:comp :task :deferred]]
    (testing kind
      (let [divergences (atom [])
            p (v2/world {:verify? true :hook (verify/checking-hook divergences)})
            h (make-handle p kind) _ (v2/value h)
            id (row-id h) c (v2/fork! p)
            [target action] (capture-handle c #(v2/in-world c h))
            ;; The pin has its own tooling alias; the injected target is never
            ;; used again. This tests allowance retirement, not alias accounting.
            pin-handle (v2/in-world c h)]
        (try
          (v2/pin! pin-handle)
          (let [before (snapshot (raw-row c id)) parent-before (snapshot (raw-row p id))]
            (is (= [1 1] [(:handles before) (:refs before)]))
            (action)
            (is (= [0 1] ((juxt :handles :refs) (snapshot (raw-row c id)))))
            (is (= parent-before (snapshot (raw-row p id))))
            (is (empty? @divergences) (str @divergences))
            (let [log-size (count (aget ^objects c rw/W-LOG))]
              (action)
              (is (= log-size (count (aget ^objects c rw/W-LOG))))))
          (v2/unpin! pin-handle)
          (is (nil? (raw-row c id)))
          (is (= :kept (v2/value h)))
          (finally
            (hs/fence! [h target pin-handle])
            (v2/release-world! c)
            (v2/release-world! p)))))))

(deftest stale-collection-does-not-register-a-retired-row
  (let [p (v2/world {:verify? true}) h (make-handle p :comp)
        _ (v2/value h) id (row-id h) c (v2/fork! p)
        [target action] (capture-handle c #(v2/in-world c h))
        other (v2/in-world c h)]
    (try
      (v2/release! other)
      (is (nil? (raw-row c id)))
      (let [parent-before (snapshot (raw-row p id))]
        (action)
        (is (nil? (raw-row c id)))
        (is (= parent-before (snapshot (raw-row p id))))
        (is (empty? (verify/violations c))))
      (finally
        (hs/fence! [h target other])
        (v2/release-world! c)
        (v2/release-world! p)))))

(deftest collection-after-world-release-preserves-host-rejection
  (let [w (v2/world {:verify? true})
        [target action] (capture-handle w #(make-handle w :comp))]
    (v2/release-world! w)
    (let [registered (set (hs/mkeys (aget ^objects w rw/W-REG)))]
      (is (true? (try (action) false
                      (catch clojure.lang.ExceptionInfo e (:spindel/released (ex-data e))))))
      (is (= registered (set (hs/mkeys (aget ^objects w rw/W-REG))))))
    (is (nil? (action)) "the original dropped flag makes a repeated notification inert")
    (hs/fence! target)))

(deftest collection-between-forked-offload-result-and-parent-commit
  ;; The same in-world/value bridge used by port.parallel-test, with one
  ;; fixed ordering. The target alias is not used after the injected event.
  (let [divergences (atom [])
        p (v2/world {:verify? true :hook (verify/checking-hook divergences)})
        model (binding [v2/*world* p] (spin (* 5 6)))
        id (row-id model) c (v2/fork! p) sibling (v2/fork! p)
        sh (v2/in-world sibling model)
        prepared (promise) finish (promise) result (promise)
        work (binding [v2/*world* p]
               (comb/parallel
                (comb/blocking
                 #(let [[target action] (capture-handle c (fn [] (v2/in-world c model)))
                        value (v2/value target)]
                    (deliver prepared action)
                    (deref finish 5000 ::timeout)
                    (hs/fence! target)
                    value))
                (comb/blocking #(v2/value sh))))]
    (try
      (v2/value-async work #(deliver result [%1 %2]))
      (let [action (deref prepared 2000 nil)]
        (is (some? action))
        (when action
          (is (not (identical? (raw-row p id) (raw-row c id))))
          (is (= 1 (:handles (snapshot (raw-row c id)))))
          (let [before (mapv #(snapshot (raw-row % id)) [p sibling])]
            (action)
            (is (nil? (raw-row c id)))
            (is (= before (mapv #(snapshot (raw-row % id)) [p sibling])))
            (checkpoint! p)
            (checkpoint! sibling)
            (is (empty? @divergences) (str @divergences)))))
      (deliver finish true)
      (is (= [[30 30] false] (deref result 2000 ::timeout)))
      (is (= 30 (v2/value model)))
      (is (= 30 (v2/value sh)))
      (finally
        (deliver finish true)
        (hs/fence! [model sh work])
        (doseq [w [c sibling p]] (v2/release-world! w))))))
