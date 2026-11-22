(ns org.replikativ.spindel.v2.yggdrasil-fork-init-test
  "The layer's `fork!` passes `:init-state` to the engine fork: the child's
   first slice sees it, also when the family's atom maintenance enters the
   child at its publication (forced: a stale sweep generation, maintenance
   run synchronously on its own thread, handoffs run in the submitting
   thread)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.ygg-support :as s :refer [dh-system done! with-stores]]
            [org.replikativ.spindel.v2.yggdrasil :as ygg]))

(defn- on-thread [nm f]
  (let [t (Thread. ^Runnable f ^String nm)] (.start t) (.join t 5000) nil))

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 400) false :else (do (Thread/sleep 5) (recur (inc n))))))

(deftest a-layer-fork-initializes-the-childs-first-slice
  (with-stores
    (let [mode (atom :inline)
          parked (java.util.concurrent.ConcurrentLinkedQueue.)
          ;; runs handoffs in the submitting thread, or parks them
          ex (reify java.util.concurrent.Executor
               (execute [_ r] (if (= :inline @mode) (.run ^Runnable r) (.add parked r))))
          w (v2/world {:executor ex :inline? false})
          kb (dh-system "kb")
          seen (atom [])
          queued #(count (seq (aget ^objects w rw/W-INGRESS)))]
      (ygg/register! w kb {})
      (swap! (:generation (aget ^objects w rw/W-FAMILY)) inc)   ; stale for every copy
      (with-redefs [hs/metadata-later! (fn ([f] (on-thread "test-maintenance" f))
                                         ([f _] (on-thread "test-maintenance" f)))]
        (reset! mode :park)
        ;; the task's creation and the fork are processed in one turn, so the
        ;; child inherits the task as runnable work
        (binding [v2/*world* w]
          (task (let [cw (v2/current-world)]
                  (swap! seen conj [(v2/world-id cw) (v2/world-state cw) (.getName (Thread/currentThread))]))))
        (let [fut (future (ygg/fork! w {:init-state (fn [st {:keys [world-id]}] (assoc st ::k world-id))}))]
          (is (wait-until #(= 2 (queued))) "the task's creation and the fork are queued")
          (reset! mode :inline)
          (loop [] (when-let [r (.poll parked)] (.run ^Runnable r) (recur)))
          (let [f (deref fut 5000 ::timeout)
                c (:world f)
                cid (v2/world-id c)
                [_ st thread] (first (filter #(= cid (first %)) @seen))]
            (is (= "test-maintenance" thread) "the child was entered at its publication")
            (is (= cid (::k st)) "its first slice sees the initial state, with its own id")
            (is (= cid (::k (v2/world-state c))))
            (is (nil? (::k (v2/world-state w))) "the parent's state is unchanged")
            (ygg/discard! f {})))
        (is (= :init-state (:spindel/invalid
                            (ex-data (try (ygg/fork! w {:owner (v2/fork! w) :init-state (fn [st _] st)}) nil
                                          (catch clojure.lang.ExceptionInfo e e)))))
            "not with another owner")
        (done! w)))))
