(ns org.replikativ.spindel.geschichte-fork-diff-test
  (:require [clojure.test :refer [deftest is]]
            [datahike.api :as d]
            [geschichte.repo :as repo]
            [geschichte.workspace :as workspace]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [yggdrasil.adapters.geschichte :as adapter]))

(defn- commit! [conn path text]
  (repo/write! conn path (.getBytes ^String text "UTF-8"))
  (repo/stage! conn [path])
  (repo/commit! conn {:message (str "Write " path)}))

(defn- with-repository [f]
  (let [cfg {:store {:backend :memory :id (random-uuid)}
             :schema-flexibility :write :keep-history? true :commit-graph? true}
        ctx (context/create-execution-context)
        forks (atom [])]
    (d/create-database cfg)
    (let [conn (d/connect cfg)]
      (try
        (repo/init! conn)
        (commit! conn "base.txt" "base")
        (binding [ec/*execution-context* ctx]
          (ygg/register! (adapter/create conn {:system-name "files"}))
          (f {:ctx ctx :conn conn
              :fork! (fn [parent]
                       (let [handle (binding [ec/*execution-context* parent] (ygg/fork!))]
                         (swap! forks conj handle)
                         handle))}))
        (finally
          (doseq [handle (reverse @forks)]
            (when (ygg/open-fork? handle) (ygg/discard-fork! handle)))
          (context/stop-context! ctx)
          (d/release conn)
          (d/delete-database cfg))))))

(defn- fork-conn [handle]
  (binding [ec/*execution-context* (:child-ctx handle)]
    (:conn (ygg/system "files"))))

(defn- changed-paths [handle]
  (let [delta (get (ygg/fork-diff handle) "files")]
    (is (nil? (:error delta)) (str (:error delta)))
    (set (map :path (:files delta)))))

(deftest parent-advance-does-not-invalidate-retained-child-diff
  (with-repository
    (fn [{:keys [ctx conn fork!]}]
      (let [handle (fork! ctx)
            child (fork-conn handle)]
        (commit! child "child.txt" "child")
        (is (= #{"child.txt"} (changed-paths handle)))
        (commit! conn "parent.txt" "parent")
        (let [before [(d/commit-id @conn) (d/commit-id @child) (workspace/list conn)]
              parent-tip (:geschichte.commit/id (repo/head-commit conn))]
          (is (nil? (repo/commit-by-id child parent-tip)))
          (is (= #{"child.txt"} (changed-paths handle)))
          (is (= before [(d/commit-id @conn) (d/commit-id @child) (workspace/list conn)])
              "Inspection must not refresh, publish, commit or remove a workspace")
          (is (ygg/open-fork? handle)))))))

(deftest nested-forks-compare-their-own-catalogs
  (with-repository
    (fn [{:keys [ctx conn fork!]}]
      (let [outer (fork! ctx)
            outer-conn (fork-conn outer)]
        (commit! outer-conn "outer.txt" "outer")
        (let [inner (fork! (:child-ctx outer))
              inner-conn (fork-conn inner)]
          (commit! inner-conn "inner.txt" "inner")
          (commit! outer-conn "outer-parent.txt" "outer parent")
          (commit! conn "trunk.txt" "trunk")
          (is (= #{"inner.txt"} (changed-paths inner)))
          (is (= #{"outer.txt" "outer-parent.txt"} (changed-paths outer)))
          (is (every? ygg/open-fork? [outer inner])))))))

(deftest observed-parent-history-is-not-counted-as-child-work
  (with-repository
    (fn [{:keys [ctx conn fork!]}]
      (let [handle (fork! ctx)]
        (commit! conn "observed-parent.txt" "observed")
        ;; The workspace's supported fast-forward imports newly observed parent
        ;; history, while the overlay's creation-time base remains unchanged.
        (workspace/advance! conn (fork-conn handle))
        (let [child (fork-conn handle)]
          (commit! child "child.txt" "child")
          (commit! conn "later-parent.txt" "later")
          (is (= #{"child.txt"} (changed-paths handle)))
          (is (ygg/open-fork? handle)))))))
