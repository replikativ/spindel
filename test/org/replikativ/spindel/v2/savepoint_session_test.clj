(ns org.replikativ.spindel.v2.savepoint-session-test
  "§8.2 S3 owners, S8 consume, S9 dispose, and effect-site addresses."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.verify :as verify]))

(def ^:dynamic *divergences* nil)

(defn- vworld []
  (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- outcome [w h]
  (try [:ok (v2/value (v2/in-world w h) 2000 ::timeout)] (catch Exception e [:err (ex-data e)])))

(defn- settle [] (Thread/sleep 50))

(deftest an-instance-outlives-its-publication-world-with-another-owner
  (checked
   (let [root (vworld)
         pubs (atom [])
         src (v2/fork! root)]
     (v2/install-handlers! src {:s (fn [p] (swap! pubs conj p))})
     (let [t (binding [v2/*world* src] (task (inc (v2/savepoint :s nil))))]
       (settle)
       (let [p (first @pubs)
             i (doto (v2/instantiate p root) (v2/activate! 41))]
         (v2/abandon! p)
         (v2/release-world! src)
         (is (= [:ok 42] (outcome i t)) "the instance belongs to root, not to the released source")
         (v2/release-world! i)))
     (v2/release-world! root))))

(deftest consume-continues-only-in-the-instances
  (checked
   (let [root (vworld)
         pubs (atom [])
         cleaned (atom [])
         src (v2/fork! root)]
     (v2/install-handlers! src {:s (fn [p] (swap! pubs conj p))})
     (let [t (binding [v2/*world* src]
               (task (try (* 10 (v2/savepoint :s nil))
                          (finally (swap! cleaned conj :finally)))))]
       (settle)
       (let [p (first @pubs)
             [a b] (v2/consume p 2 root)]
         (v2/activate! a 1)
         (v2/activate! b 2)
         (is (= [:ok 10] (outcome a t)))
         (is (= [:ok 20] (outcome b t)))
         (is (= [:finally :finally] @cleaned) "once per instance")
         (v2/resume! p 99)
         (v2/abandon! p)
         (v2/release-world! src)
         (settle)
         (is (= [:finally :finally] @cleaned) "never in the source world, even when it is released")
         (is (thrown? Exception (v2/consume p 1 root)) "a consumed savepoint is not pending")
         (v2/release-world! a) (v2/release-world! b)))
     (v2/release-world! root))))

(deftest dispose-drops-the-anchor
  (checked
   (let [w (vworld)
         pubs (atom [])]
     (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
     (binding [v2/*world* w]
       (let [t (task (inc (v2/savepoint :s 1)))]
         (settle)
         (let [p (first @pubs)]
           (v2/resume! p 1)
           (is (= 2 (v2/value t 1000 ::timeout)))
           (testing "a resumed publication is still an anchor"
             (let [i (doto (v2/instantiate p) (v2/activate! 5))]
               (is (= [:ok 6] (outcome i t)))
               (v2/release-world! i)))
           (v2/dispose! p)
           (is (nil? (:basis p)))
           (is (thrown? Exception (v2/instantiate p w)))))
       (let [t (task (v2/savepoint :s 2))]
         (settle)
         (v2/dispose! (second @pubs))
         (is (:spindel/cancelled (second (outcome w t))) "a pending publication is abandoned first"))))))

(def seen (atom []))
(v2/register-effect! `probe (fn [_ ctx] (swap! seen conj [(:frame ctx) (:key ctx)]) [:value nil]))
(defn probe [] (throw (ex-info "probe outside a body" {})))

(deftest effect-sites-carry-key-and-frame
  (reset! seen [])
  (let [w (v2/world)]
    (binding [v2/*world* w]
      (let [t (task (loop [i 0] (when (< i 2) (probe) (recur (inc i))))
                    (v2/await (task (probe)))
                    :done)]
        (is (= :done (v2/value t 1000 ::timeout)))
        (let [[[f0 k0] [f1 k1] [f2 _]] @seen]
          (is (= [] f0 f1) "a host-created task has an empty frame")
          (is (= 1 (- k1 k0)) "one site, consecutive ordinals")
          (is (= 1 (count f2)) "a nested task's frame holds its creation key"))))
    (v2/release-world! w)))

(deftest an-instance-continues-the-ordinal-count
  (reset! seen [])
  (let [w (v2/world) pubs (atom [])]
    (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
    (binding [v2/*world* w]
      (let [t (task (probe) (v2/savepoint :s nil) (probe) :ok)]
        (settle)
        (let [p (first @pubs)
              i (doto (v2/instantiate p) (v2/activate! nil))]
          (is (= [:ok :ok] (outcome i t)))
          (v2/resume! p nil)
          (is (= :ok (v2/value t 1000 ::timeout)))
          (let [ks (mapv second @seen)]
            (is (= 3 (count ks)))
            (is (= (nth ks 1) (nth ks 2)) "the second probe has the same key in the instance and in place")
            (is (not= (nth ks 0) (nth ks 1))))
          (v2/release-world! i))))
    (v2/release-world! w)))
