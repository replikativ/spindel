(ns org.replikativ.spindel.v2.lifetime-gc-test
  "Real host reachability supplements the deterministic lifetime fixtures."
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.rows :as rw]))

(defn- eventually [f]
  (loop [n 0]
    (cond (f) true
          (= n 200) false
          :else (do (System/gc) (Thread/sleep 25) (recur (inc n))))))

(defn- self-watches [w]
  (binding [v2/*world* w]
    (let [a (v2/atom :value) s (v2/signal :value)]
      (add-watch a :self (fn [_ _ _ _] (hs/fence! a)))
      (add-watch s :self (fn [_ _ _ _] (hs/fence! s)))
      [(hs/weak a) (hs/weak s)])))

(deftest self-capturing-watches-do-not-root-their-objects
  (doseq [verify? [false true]]
    (let [w (v2/world {:verify? verify?}) refs (self-watches w)]
      (try
        (is (eventually #(every? (comp nil? hs/deref-weak) refs)))
        (is (eventually #(and (empty? (aget ^objects w rw/W-ATOMS))
                              (zero? (hs/msize (aget ^objects w rw/W-WATCHES))))))
        (finally (v2/release-world! w))))))

(defn- atoms-in-idle-forks [p]
  (binding [v2/*world* p]
    (let [a (v2/atom :a) b (v2/atom :b)
          worlds [(v2/fork! p) (v2/fork! p)]]
      {:atoms [(hs/weak a) (hs/weak b)] :worlds worlds})))

(deftest dead-atoms-are-pruned-from-multiple-idle-forks
  (let [p (v2/world) {:keys [atoms worlds]} (atoms-in-idle-forks p)]
    (try
      (is (eventually #(every? (comp nil? hs/deref-weak) atoms)))
      (is (eventually #(every? (fn [w] (empty? (aget ^objects w rw/W-ATOMS))) (cons p worlds))))
      (finally (doseq [w worlds] (v2/release-world! w)) (v2/release-world! p)))))

(defn- atom-watch-in-dropped-world [p a]
  (let [c (v2/fork! p)]
    (binding [v2/*world* c] (add-watch a :child (fn [& _])))
    (hs/weak c)))

(deftest live-atom-does-not-retain-dead-world-capsules
  (let [p (v2/world) a (binding [v2/*world* p] (v2/atom 0))
        wc (atom-watch-in-dropped-world p a)
        owner (.-watch-owner ^org.replikativ.spindel.v2.core.RAtom a)]
    (try
      (is (eventually #(nil? (hs/deref-weak wc))))
      (is (eventually #(zero? (hs/msize (:capsules owner)))))
      (is (eventually #(= 1 (hs/msize (:worlds (aget ^objects p rw/W-FAMILY))))))
      (finally (v2/release-world! p)))))

(defn- make-alias [w s]
  (v2/in-world w s))

(deftest surviving-alias-keeps-watches-after-registration-alias-collection
  (let [w (v2/world {:verify? true})
        s (binding [v2/*world* w] (v2/signal 0))
        alias (make-alias w s) seen (atom [])
        registered (let [other (make-alias w s)]
                     (add-watch other :k (fn [_ _ o n] (swap! seen conj [o n])))
                     (hs/weak other))]
    (try
      (is (eventually #(nil? (hs/deref-weak registered))))
      (reset! alias 1)
      (is (= [[0 1]] @seen))
      (remove-watch alias :k)
      (is (empty? (.getWatches ^clojure.lang.IRef s)))
      (finally (v2/release-world! w)))))

(deftest user-value-reachability-is-intentionally-strong
  (let [w (v2/world)
        holder (binding [v2/*world* w]
                 (let [a (v2/atom nil)] (reset! a a) (hs/weak a)))]
    ;; This is the documented boundary: W-ATOMS values own arbitrary user data.
    (dotimes [_ 3] (System/gc))
    (is (some? (hs/deref-weak holder)))
    (v2/release-world! w)
    (is (eventually #(nil? (hs/deref-weak holder))))))

(defn- foreign-watch [p s]
  (let [c (v2/fork! p)]
    (binding [v2/*world* c]
      (v2/task (add-watch s :foreign (fn [& _]))))
    (hs/weak c)))

(deftest live-invoking-handle-does-not-retain-its-foreign-world
  (let [p (v2/world) s (binding [v2/*world* p] (v2/signal 0))
        wc (foreign-watch p s)
        o (:foreign-owner (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle s) 2))]
    (try
      (is (eventually #(nil? (hs/deref-weak wc))))
      (is (eventually #(zero? (hs/msize (:capsules o)))))
      (is (v2/handle? s))
      (finally (v2/release-world! p)))))

(defn- foreign-alias-churn [p c s]
  (dotimes [_ 100]
    (let [h (v2/in-world p s)]
      (binding [v2/*world* c] (v2/task (add-watch h :k (fn [& _])))))))

(deftest weak-owner-memberships-shrink-after-alias-churn
  (let [p (v2/world) s (binding [v2/*world* p] (v2/signal 0))
        c (v2/fork! p) child-source (v2/in-world c s)
        token (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle child-source) 1)]
    (try
      (foreign-alias-churn p c s)
      (is (eventually #(zero? (hs/msize (:owners token)))))
      (is (= #{:k} (set (keys (.getWatches ^clojure.lang.IRef child-source)))))
      (finally (v2/release-world! c) (v2/release-world! p)))))

(defn- self-valued-source-world []
  (let [w (v2/world {:verify? true}) s (binding [v2/*world* w] (v2/signal nil))]
    (reset! s s)
    [(hs/weak w) (hs/weak s)]))

(deftest collection-actions-do-not-root-a-self-valued-source-world
  (let [refs (self-valued-source-world)]
    (is (eventually #(every? (comp nil? hs/deref-weak) refs)))))

(defn- child-alias-of-self-watched-parent [p]
  (let [s (binding [v2/*world* p] (v2/signal :value))
        token (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle s) 1)
        c (v2/fork! p)]
    (add-watch s :self (fn [& _] (hs/fence! s)))
    {:alias (v2/in-world c s) :refs [(hs/weak s) (hs/weak token)] :child c}))

(deftest child-alias-does-not-own-the-parents-callback-map
  (doseq [verify? [false true]]
    (let [p (v2/world {:verify? verify?})
          {:keys [alias refs child]} (child-alias-of-self-watched-parent p)]
      (try
        (is (eventually #(every? (comp nil? hs/deref-weak) refs)))
        (is (empty? (.getWatches ^clojure.lang.IRef alias)))
        (is (= :value (v2/value alias)))
        (finally (v2/release-world! child) (v2/release-world! p))))))

(defn- ref-to-self-watched-source [p]
  (let [s (binding [v2/*world* p] (v2/signal :value))]
    (add-watch s :self (fn [& _] (hs/fence! s)))
    {:ref (v2/world-ref s) :wrapper (hs/weak s)}))

(deftest world-neutral-ref-does-not-retain-a-source-watch-cycle
  (let [p (v2/world) {:keys [ref wrapper]} (ref-to-self-watched-source p)]
    (try
      (is (eventually #(nil? (hs/deref-weak wrapper))))
      (let [alias (v2/resolve-ref p ref)]
        (is (= :value (v2/value alias)))
        (is (empty? (.getWatches ^clojure.lang.IRef alias))))
      (finally (v2/release-world! p)))))

(defn- temporary-computation-alias [c parent-handle]
  (let [h (v2/in-world c parent-handle)]
    (v2/value h)
    (hs/weak h)))

(deftest collected-fork-alias-preserves-parent-and-sibling-handles
  ;; Actual weak-unreachability complements handle-collection-test's injected
  ;; callbacks. Keep the parent's handle and sibling alias fenced throughout.
  (let [p (v2/world {:verify? true})
        h (binding [v2/*world* p] (v2/spin :kept))
        _ (v2/value h)
        id (aget ^objects (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle h) 0) rw/ID)
        c (v2/fork! p) sibling (v2/fork! p)
        sh (v2/in-world sibling h) target (temporary-computation-alias c h)]
    (try
      (is (eventually #(nil? (hs/deref-weak target))))
      (is (eventually #(nil? (hs/mget (aget ^objects c rw/W-REG) id))))
      (doseq [w [p sibling]]
        (is (= 1 (aget ^objects (hs/mget (aget ^objects w rw/W-REG) id) rw/HANDLES))))
      (is (= :kept (v2/value h)))
      (is (= :kept (v2/value sh)))
      (finally
        (hs/fence! [h sh])
        (doseq [w [c sibling p]] (v2/release-world! w))))))
