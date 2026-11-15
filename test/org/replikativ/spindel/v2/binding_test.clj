(ns org.replikativ.spindel.v2.binding-test
  "Dynamic bindings belong to the run (JVM): a body runs with its creator's
   frame, a `binding` may span effects, and neither the resuming thread's
   bindings leak in nor the body's leak out. Forks copy the run's frame."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await]]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)
(def ^:dynamic *x* :root)

(defn- vworld
  ([] (vworld true))
  ([inline?] (v2/world {:verify? true :inline? inline? :hook (verify/checking-hook *divergences*)})))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- v [h] (v2/value h 2000 ::timeout))
(defn- parked [] (Thread/sleep 50))

(deftest a-task-runs-with-its-creators-bindings
  (doseq [inline? [true false]]
    (testing (if inline? "inline world" "drainer world")
      (checked
       (let [w (vworld inline?)]
         (binding [v2/*world* w]
           (let [d (v2/deferred)
                 t (binding [*x* :creator] (task (let [a *x*] (await d) [a *x*])))]
             (parked)
             (binding [*x* :deliverer] (v2/deliver! d :go))
             (is (= [:creator :creator] (v t)) "the deliverer's binding does not leak in")))
         (v2/release-world! w))))))

(deftest a-binding-spans-effects-on-any-thread
  (doseq [inline? [true false]]
    (testing (if inline? "inline world" "drainer world")
      (checked
       (let [w (vworld inline?)]
         (binding [v2/*world* w]
           (let [d (v2/deferred)
                 t (task (binding [*x* :inner] (let [a *x*] (await d) [a *x*])))]
             (parked)
             (is (= :root *x*) "a parked body's binding does not leak onto the host thread")
             (is (= :future @(future (binding [*x* :future] (v2/deliver! d :go) *x*)))
                 "resuming on another thread leaves that thread's frame alone")
             (is (= [:inner :inner] (v t)))
             (is (= :root *x*))))
         (v2/release-world! w))))))

(deftest a-binding-exits-to-the-creators-frame
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             t (binding [*x* :creator]
                 (task (let [a (binding [*x* :inner] (await d) *x*)] [a *x*])))]
         (parked)
         (v2/deliver! d :go)
         (is (= [:inner :creator] (v t)))))
     (v2/release-world! w))))

(deftest a-child-task-starts-from-its-creators-live-frame
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             t (task (let [c (binding [*x* :inner] (task (await d) *x*))]
                       (await c)))]
         (parked)
         (v2/deliver! d :go)
         (is (= :inner (v t)) "the child keeps the binding after the parent's form exits")))
     (v2/release-world! w))))

(deftest a-computation-reruns-with-its-creators-bindings
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)
             seen (atom [])
             c (binding [*x* :creator] (spin [(iv/get-new (track x)) *x*]))
             unobserve (v2/observe! c (fn [val _] (swap! seen conj val)))]
         @(future (binding [*x* :writer] (v2/write! x 2)))
         (Thread/sleep 50)
         (is (= [[1 :creator] [2 :creator]] @seen) "the writer's binding does not reach the rerun")
         (unobserve)))
     (v2/release-world! w))))

(deftest cancelling-inside-a-binding-unwinds-on-the-runs-frame
  (checked
   (let [w (vworld)
         cleaned (promise)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             t (task (binding [*x* :inner]
                       (try (await d) (finally (deliver cleaned *x*)))))]
         (parked)
         (binding [*x* :canceller] (v2/cancel-task! t))
         (is (= :inner (deref cleaned 2000 ::timeout)) "the finally runs with the run's bindings")
         (is (= :root *x*))))
     (v2/release-world! w))))

(deftest a-host-fork-copies-the-runs-frame
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             t (binding [*x* :creator]
                 (task (let [a (binding [*x* :inner] [(await d) *x*])] [a *x*])))
             _ (parked)
             child (v2/fork! w)]
         (binding [*x* :fork-deliverer] (v2/deliver! (v2/in-world child d) :c))
         (v2/deliver! d :p)
         (is (= [[:p :inner] :creator] (v t)))
         (is (= [[:c :inner] :creator] (v (v2/in-world child t))) "the fork resumes on its copy of the frame")))
     (v2/release-world! w))))

(deftest the-fork-effect-carries-the-live-frame
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [out (promise)
             gate (v2/deferred)
             t (binding [*x* :creator]
                 (task (let [r (binding [*x* :inner]
                                 (let [[side child] (v2/fork)]
                                   (when child (deliver out child))
                                   (when (= side :parent) (await gate))
                                   [side *x*]))]
                         [r *x*])))
             child (deref out 2000 nil)
             in-child (v (v2/in-world child t))]
         (v2/deliver! gate :go)
         (is (= [[:child :inner] :creator] in-child) "the child's copy resumes inside the binding")
         (is (= [[:parent :inner] :creator] (v t)))))
     (v2/release-world! w))))

(deftest a-savepoint-instance-continues-with-the-live-frame
  (checked
   (let [root (vworld)
         pubs (atom [])
         src (v2/fork! root)]
     (v2/install-handlers! src {:s (fn [p] (swap! pubs conj p))})
     (let [t (binding [v2/*world* src *x* :creator]
               (task (let [r (binding [*x* :inner] [(v2/savepoint :s nil) *x*])] [r *x*])))]
       (parked)
       (let [p (first @pubs)
             i (doto (v2/instantiate p root) (v2/activate! 7))]
         (is (= [[7 :inner] :creator] (v (v2/in-world i t))))
         (v2/abandon! p)
         (v2/release-world! i)))
     (v2/release-world! src)
     (v2/release-world! root))))
