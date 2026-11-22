(ns org.replikativ.spindel.v2.fork-init-cljc-test
  "`fork!` with `:init-state` on both platforms (spec §8.1 F): the child's
   world state starts initialized, and the child is published after the
   fork commits. CLJS: the synchronous reply (an inline world, also from a
   host item of the forked world, H1) and the queued reply (a non-inline
   world: `host-call!` cannot answer synchronously and throws, while the
   fork item still runs, commits and hands the child off). The CLJS cases
   complete from the child's first slice."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is async]])
            [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]))

(defn- member? [w id]
  (some? (hs/mget (:worlds (aget ^objects w rw/W-FAMILY)) id)))

(defn- fork-ids [w]
  (vec (keep #(when (= :fork-host (first (:item %))) (second (:item %))) (aget ^objects w rw/W-LOG))))

(deftest a-synchronous-fork-starts-from-its-initial-state
  (let [w (v2/world {:verify? true})
        _ (v2/swap-world! w assoc :a 1)
        c (v2/fork! w {:init-state (fn [s _] (assoc s :k :sync))})
        cid (v2/world-id c)]
    (is (= {:a 1 :k :sync} (v2/world-state c)))
    (is (= {:a 1} (v2/world-state w)) "the source is unchanged")
    (is (= [cid] (fork-ids w)) "committed")
    (is (member? w cid) "published")
    (v2/release-world! c)
    (v2/release-world! w)))

(deftest a-throwing-initializer-is-the-forks-throw
  (let [w (v2/world {:verify? true})
        e (try (v2/fork! w {:init-state (fn [_ _] (throw (ex-info "init" {::init true})))}) nil
               (catch #?(:clj Exception :cljs :default) e e))]
    (is (::init (ex-data e)))
    (is (= [] (fork-ids w)) "nothing committed")
    (v2/release-world! w)))

#?(:cljs
   (deftest an-initializer-throwing-nil-or-false-is-the-forks-throw
     (doseq [x [nil false]]
       (let [w (v2/world {:verify? true})
             r (try (v2/fork! w {:init-state (fn [_ _] (throw x))}) [:returned]
                    (catch :default e [:threw e]))]
         (is (= [:threw x] r) "the reply's tag, not the thrown value, tells a throw")
         (is (= [] (fork-ids w)) "nothing committed")
         (v2/release-world! w)))))

(defn- signal-done
  "Completes an async test from a slice: after the slice's gate is left
   (cljs.test starts the next test synchronously from `done`)."
  [done]
  #?(:cljs (js/setTimeout done 0) :clj (done)))

(defn- child-slice
  "A task body for the world `w`'s turn: in a child of `w`, `(f child-id
   state)` (the child's first slice signals the test's completion)."
  [w f]
  (let [cw (v2/current-world)
        id (v2/world-id cw)]
    (when-not (= id (v2/world-id w))
      (f id (v2/world-state cw)))))

#?(:cljs
   (deftest a-fork-from-a-host-item-replies-synchronously
     (async done
            (let [w (v2/world {:verify? true})
                  cid (atom nil)
                  c (v2/host-call! w (fn []
                                       (binding [v2/*world* w]
                                         (task (child-slice w (fn [id st]
                                                                (is (= @cid id) "the child's copy of the task")
                                                                (is (= {:k :held} st) "sees its initial state")
                                                                (signal-done done)))))
                                       (v2/fork! w {:init-state (fn [s _] (assoc s :k :held))})))]
              (reset! cid (v2/world-id c))
              (is (= {:k :held} (v2/world-state c)))
              (is (= [@cid] (fork-ids w)))
              (is (member? w @cid))))))

#?(:cljs
   (deftest a-queued-fork-still-commits-and-hands-off
     (async done
            (let [w (v2/world {:inline? false :verify? true})
                  ;; queued before the fork: the fork item finds the task runnable
                  _ (binding [v2/*world* w]
                      (task (child-slice w (fn [id st]
                                             (is (= [id] (fork-ids w)) "the queued fork item committed")
                                             (is (member? w id) "published")
                                             (is (= {:k :queued} st) "the child sees its initial state")
                                             (signal-done done)))))
                  e (try (v2/fork! w {:init-state (fn [s _] (assoc s :k :queued))}) nil
                         (catch :default e e))]
              (is (re-find #"synchronously" (ex-message e)) "the reply is not synchronous")
              (is (= [] (fork-ids w)) "nothing ran yet")))))
