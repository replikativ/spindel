(ns org.replikativ.spindel.v2.lifecycle-test
  "Fork ownership (F2) and abandonment (S7): lifecycle design v2 E1-E6."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await sleep]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]))

(def ^:dynamic *divergences* nil)

(defn- vworld
  ([] (vworld {}))
  ([opts] (v2/world (merge {:verify? true :hook (verify/checking-hook *divergences*)} opts))))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 500) false :else (do (Thread/sleep 5) (recur (inc n))))))

(defn- collected?
  "Collects until every weak reference in `ws` is cleared (or gives up)."
  [ws]
  (loop [n 0]
    (cond (every? #(nil? (.get ^java.lang.ref.WeakReference %)) ws) true
          (> n 40) false
          :else (do (System/gc) (Thread/sleep 25) (recur (inc n))))))

(defn- outcome [h]
  (try [:ok (v2/value h 1000 ::timeout)] (catch Exception e [:err (ex-data e)])))

(deftest owner-close-releases-a-fork
  ;; F2: a fork made in a task is owned by its scope; the task's end releases
  ;; the child, cancelling its timer loop and running its finally
  (checked
    (let [w (vworld) fin (atom nil)]
      (binding [v2/*world* w]
        (let [gate (v2/deferred)
              t (task (let [[side _] (v2/fork)]
                        (if (= side :child)
                          (try (loop [] (sleep 5) (recur)) (finally (reset! fin :ran)))
                          (await gate))))]
          (Thread/sleep 50)
          (is (nil? @fin) "the child's loop runs while its owner lives")
          (v2/deliver! gate :go)
          (is (= [:ok :go] (outcome t)))
          (is (wait-until #(= :ran @fin)) "the owner's end released the child and ran its finally"))))))

(defn- stuck-fork!
  "A host fork with a run parked on a deferred nobody else can deliver."
  [w fin]
  (let [c (v2/fork! w)
        d (v2/deferred c)]
    (binding [v2/*world* c]
      (task (try (await d) (finally (reset! fin :ran)))))
    c))

(deftest a-reachable-stuck-fork-is-released-by-its-owner
  ;; F2: the root scope's close (T21) releases the host forks still alive,
  ;; and their finalizers run
  (checked
    (let [w (vworld) fin (atom nil)
          c (stuck-fork! w fin)]
      (Thread/sleep 20)
      (is (nil? @fin))
      (v2/release-world! w)
      (is (wait-until #(= :ran @fin)) "the owner's release released the child; its finally ran")
      (is (aget ^objects c rw/W-RELEASED)))))

(deftest a-dropped-stuck-host-fork-is-collected
  ;; Z#58: a host fork that nothing can act in any more (no handle, no
  ;; resource) is collected; its parked run can never resume, so its finally
  ;; never runs. Production world: verify mode's handle cleaners hold worlds.
  (let [w (v2/world) fin (atom nil)
        probe (java.lang.ref.WeakReference. (stuck-fork! w fin))]
    (is (collected? [probe]))
    (is (nil? @fin))))

(deftest a-dropped-idle-fork-is-collected
  ;; E2: an idle fork is held weakly; dropped by the host it is collected
  (checked
    (let [w (vworld)
          probes (vec (repeatedly 20 #(java.lang.ref.WeakReference. (v2/fork! w))))]
      (is (collected? probes)))))

(defn- unborn-instances [p n]
  (vec (repeatedly n #(java.lang.ref.WeakReference. (v2/instantiate p)))))

(deftest a-dropped-unactivated-instance-runs-nothing
  ;; E4: an instance is unborn until activate!: dropped, it is collected without
  ;; activating its inherited timer or running the copied finalizers
  (checked
    (let [w (vworld) fin (atom 0) pubs (atom [])]
      (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
      (binding [v2/*world* w]
        (let [loop-t (task (try (loop [] (sleep 5) (recur)) (finally (swap! fin inc))))
              sp (task (v2/savepoint :s nil))]
          (is (wait-until #(seq @pubs)))
          (let [probes (unborn-instances (first @pubs) 20)]
            (is (collected? probes) "inherited timers stayed dormant: nothing kept them alive")
            (is (zero? @fin) "no copied finalizer ran"))
          (v2/abandon! (first @pubs))
          (v2/cancel-task! loop-t)
          (is (wait-until #(= 1 @fin)) "only the source's own finalizer runs")
          (is (:spindel/cancelled (second (outcome sp)))))))))

(deftest activated-instances-are-owned-then-collected
  ;; E4/E2: activation gives the instance its marker; once its runs retire it
  ;; is idle, and a dropped batch is collected with no further parent activity
  (checked
    (let [w (vworld) pubs (atom [])]
      (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
      (binding [v2/*world* w]
        (let [t (task (inc (v2/savepoint :s nil)))]
          (is (wait-until #(seq @pubs)))
          (let [p (first @pubs)
                probes (vec (for [i (range 20)]
                              (let [c (doto (v2/instantiate p) (v2/activate! i))]
                                (is (= [:ok (inc i)] (outcome (v2/in-world c t))))
                                (java.lang.ref.WeakReference. c))))]
            (is (collected? probes) "a finished particle the host dropped is collected"))
          (v2/abandon! (first @pubs)))))))

(defn- publish-and-drop! [w]
  (binding [v2/*world* w]
    (task (v2/savepoint :s nil))))

(deftest a-dropped-pending-publication-abandons
  ;; S7: the handler drops the publication without resuming: the run is
  ;; cancelled with ::abandoned
  (checked
    (let [w (vworld)]
      (v2/install-handlers! w {:s (fn [_] nil)})
      (let [t (publish-and-drop! w)]
        (is (wait-until #(do (System/gc) (= [:err {:spindel/cancelled ::v2/abandoned}] (outcome t)))))))))

(deftest a-resumed-publication-drops-quietly
  (checked
    (let [w (vworld)]
      (v2/install-handlers! w {:s (fn [p] (v2/resume! p 41))})
      (binding [v2/*world* w]
        (let [t (task (inc (v2/savepoint :s nil)))]
          (is (= [:ok 42] (outcome t)))
          (dotimes [_ 5] (System/gc) (Thread/sleep 10))
          (is (= [:ok 42] (outcome t)) "collection of a resumed publication changes nothing"))))))

(deftest publications-are-read-only
  (checked
    (let [w (vworld) pubs (atom [])]
      (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
      (binding [v2/*world* w]
        (let [t (task (v2/savepoint :s 7))]
          (is (wait-until #(seq @pubs)))
          (let [p (first @pubs)]
            (is (= 7 (:payload p)))
            (is (thrown? Exception (assoc p :weight 1)) "no accidental copies"))
          (v2/abandon! (first @pubs)))))))

(deftest owner-close-with-an-inline-executor
  ;; E3: children are scheduled after the parent's gate is released, so an
  ;; executor that runs tasks inline cannot hold two gates
  (checked
    (let [inline (reify java.util.concurrent.Executor (execute [_ r] (.run r)))
          w (vworld {:executor inline})
          fin (atom nil)]
      (binding [v2/*world* w]
        (let [entered (promise)
              gate (v2/deferred)
              t (task (let [[side _] (v2/fork)]
                        (if (= side :child)
                          (try (deliver entered true) (await (v2/deferred)) (finally (reset! fin :ran)))
                          (do (await gate) :parent-done))))]
          (is (deref entered 1000 false) "the child ran, scheduled after the parent's gate")
          (v2/deliver! gate :go)
          (is (= [:ok :parent-done] (outcome t)))
          (is (wait-until #(= :ran @fin)) "the child was released at the task's end"))))))
