(ns org.replikativ.spindel.v2.fork-init-test
  "Host fork with a private initial world state (`fork!` `:init-state`) and
   publication after acceptance (spec §8.1 F, H1); `instantiate` publishes
   an instance with all its birth fields set. The races are made
   deterministic: the family's atom maintenance is run synchronously on its
   own thread at registration, and the worlds' executor runs handoffs in
   the submitting thread."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.lifetime :as lt]
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
  (loop [n 0] (cond (f) true (> n 400) false :else (do (Thread/sleep 5) (recur (inc n))))))

(def caller-runs
  "An executor that runs a handoff in the submitting thread."
  (reify java.util.concurrent.Executor
    (execute [_ r] (.run ^Runnable r))))

(defn- on-thread
  "Runs `f` on a fresh thread named `nm` and waits for it."
  [nm f]
  (let [t (Thread. ^Runnable f ^String nm)]
    (.start t)
    (.join t 5000)
    nil))

(defmacro with-synchronous-maintenance
  "The family's atom maintenance runs at once, on its own thread, while the
   requesting thread waits: a registration with a stale sweep generation
   enters the new world before the registering call returns."
  [& body]
  `(with-redefs [hs/metadata-later! (fn ([f#] (on-thread "test-maintenance" f#))
                                      ([f# _#] (on-thread "test-maintenance" f#)))]
     ~@body))

(defn- stale-generation!
  "Advances the family's atom-sweep generation past every copy: a world
   registered next requests maintenance at once (lifetime/register-world!)."
  [w]
  (swap! (:generation (aget ^objects w rw/W-FAMILY)) inc))

(defn- member? [w id]
  (some? (hs/mget (:worlds (aget ^objects w rw/W-FAMILY)) id)))

(defn- committed? [w id]
  (boolean (some #(= [:fork-host id] (:item %)) (verify/log w))))

(defn- next-id [w] (#'v2/peek-id w))

(defn- recorder
  "A task body's record: [world-id world-state thread-name]."
  []
  (let [cw (v2/current-world)]
    [(v2/world-id cw) (v2/world-state cw) (.getName (Thread/currentThread))]))

(deftest instantiate-publishes-an-unborn-instance
  (checked
   (let [w (vworld {:executor caller-runs})
         pubs (atom [])
         seen (atom [])]
     (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
     ;; one host item starts two tasks: the first publishes at its savepoint
     ;; while the second is still runnable, so the basis inherits it
     (v2/host-call! w (fn []
                        (binding [v2/*world* w]
                          (task (v2/savepoint :s nil) (swap! seen conj (conj (recorder) :resumed)))
                          (task (swap! seen conj (recorder))))))
     (is (= 1 (count @pubs)))
     (stale-generation! w)
     (let [i (with-synchronous-maintenance
               (v2/instantiate (first @pubs) nil #(assoc % :k :init)))
           iid (v2/world-id i)
           mine #(filterv (fn [r] (= iid (first r))) @seen)]
       (is (member? w iid) "published")
       (is (= [] (mine)) "maintenance at registration runs no inherited work: the instance is unborn")
       (is (= {:k :init} (v2/world-state i)))
       (v2/activate! i :go)
       (is (= #{[iid {:k :init}]} (set (map #(subvec % 0 2) (mine))))
           "after activation the inherited work runs, and sees the initial state")
       (is (= 2 (count (mine))))
       (v2/abandon! (first @pubs))))))
