(ns org.replikativ.spindel.ygg-checkpoint-test
  (:require [clojure.test :refer [deftest is]]
            [datahike.api :as d]
            [geschichte.bytes :as bytes]
            [geschichte.query :as query]
            [geschichte.repo :as repo]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.world.scope :as scope]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.ygg-construction-failure-test :as fixtures]
            [yggdrasil.adapters.geschichte :as gy]
            [yggdrasil.protocols :as p]))

(defn- with-repo [f]
  (let [config {:store {:backend :memory :id (random-uuid)}
                :schema-flexibility :write :keep-history? true :commit-graph? true}
        ctx (sp/create-execution-context)]
    (d/create-database config)
    (let [conn (d/connect config)]
      (try
        (repo/init! conn)
        (sp/with-context ctx
          (ygg/register! (gy/create conn {:system-name "workspace"}))
          (f conn))
        (finally (context/stop-context! ctx) (d/release conn) (d/delete-database config))))))

(defn- commit! [conn path text]
  (repo/write! conn path (bytes/utf8 text))
  (repo/stage-all! conn)
  (repo/commit! conn {:message text :author "checkpoint-test"}))

(defn- checkpoint [conn]
  {:version 1 :kind :datahike :commit (d/commit-id @conn)
   :source {:store (get-in @conn [:config :store :id])
            :repository (:geschichte.repo/id (query/repository @conn))}})

(defn- text [conn path] (some-> (repo/read conn path) bytes/decode-utf8))
(defn- caught [f] (try (f) nil (catch Throwable error error)))

(deftest checkpoint-fork-preserves-dirty-source-state-and-recursive-child-edits
  (with-repo
    (fn [conn]
      (let [logical (:geschichte.commit/id (commit! conn "state.md" "C1"))]
        (repo/write! conn "staged.md" (bytes/utf8 "C1 staged"))
        (repo/stage-all! conn)
        (repo/write! conn "untracked.md" (bytes/utf8 "C1 untracked"))
        (let [origin (checkpoint conn)]
          (commit! conn "state.md" "C2")
          (repo/write! conn "future.md" (bytes/utf8 "C2 only"))
          (let [parent-before (vec (d/datoms @conn :eavt)) branches-before (d/branches conn)
                handle (ygg/fork! {:mode :frozen :checkpoints {"workspace" origin}})]
            (try
              (let [descriptor (get-in (ygg/fork-descriptor handle) [:fork/systems "workspace"])]
                (is (= :overlay (:kind descriptor)))
                (is (= :frozen (:mode descriptor)))
                (is (= (str logical) (:base-snapshot descriptor)))
                (is (= origin (:checkpoint descriptor))))
              (ygg/with-fork handle
                (let [selected (gy/connection (ygg/system "workspace"))]
                  (is (= "C1" (text selected "state.md")))
                  (is (= "C1 staged" (text selected "staged.md")))
                  (is (= "C1 untracked" (text selected "untracked.md")))
                  (is (nil? (text selected "future.md")))
                  (repo/write! selected "proposal.md" (bytes/utf8 "Outer edits"))
                  (let [child (ygg/fork! {:mode :frozen})]
                    (try
                      (ygg/with-fork child
                        (let [nested (gy/connection (ygg/system "workspace"))]
                          (is (= "Outer edits" (text nested "proposal.md")))))
                      (is (nil? (get-in (ygg/fork-descriptor child) [:fork/systems "workspace" :checkpoint]))
                          "An ordinary recursive fork does not replay the original checkpoint")
                      (finally (ygg/discard-fork! child))))))
              (is (= parent-before (vec (d/datoms @conn :eavt))))
              (finally (ygg/discard-fork! handle)))
            (is (= branches-before (d/branches conn)))
            (is (= "C2" (text conn "state.md")))
            (is (nil? (text conn "proposal.md")))))))))

(deftest all-checkpoint-policies-validate-before-any-native-acquisition
  (with-repo
    (fn [conn]
      (commit! conn "state.md" "basis")
      (let [origin (checkpoint conn)
            calls (atom 0) live (atom #{}) discards (atom 0) captured (atom nil)
            failure (ex-info "Unexpected ordinary allocation" {})
            branches (d/branches conn)]
        (ygg/register! (fixtures/->ProbeSystem "earlier" calls live discards captured failure (atom -1)))
        (doseq [[options expected-type]
                [[{:checkpoints false} ::ygg/invalid-checkpoint-policy]
                 [{:checkpoints {"workspace" (assoc origin :extra true)}} ::ygg/invalid-checkpoint-origin]
                 [{:systems #{"earlier"} :checkpoints {"workspace" origin}} ::ygg/excluded-checkpoint-systems]
                 [{:checkpoints {"workspace" origin} :snapshots {"workspace" "logical"}} ::ygg/overlapping-historical-policies]
                 [{:checkpoints {"earlier" origin}} ::ygg/unsupported-checkpoint-fork]
                 [{:checkpoints {"workspace" (assoc-in origin [:source :store] (random-uuid))}} nil]
                 [{:checkpoints {"workspace" (assoc-in origin [:source :repository] (random-uuid))}} nil]
                 [{:checkpoints {"workspace" (assoc origin :commit (random-uuid))}} nil]]]
          (let [error (caught #(ygg/fork! options))]
            (is (some? error))
            (when expected-type (is (= expected-type (:type (ex-data error)))))
            (is (nil? (:construction/owner (ex-data error))))
            (is (zero? @calls))
            (is (empty? @live))
            (is (= branches (d/branches conn)))))))))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [[status value :as outcome] (deref result 5000 ::timeout)]
      (when (= ::timeout outcome) (throw (ex-info "CPS timed out" {})))
      (if (= :ok status) value (throw value)))))

(deftest copying-preserves-current-checkpoint-world-edits-and-refuses-a-rewind-policy
  (with-repo
    (fn [conn]
      (commit! conn "state.md" "C1")
      (let [origin (checkpoint conn)]
        (commit! conn "state.md" "C2")
        (let [handle (ygg/fork! {:checkpoints {"workspace" origin}})
              admissions (atom 0) before (d/branches conn)]
          (ygg/with-fork handle
            (repo/write! (gy/connection (ygg/system "workspace")) "proposal.md" (bytes/utf8 "Current edits")))
          (doseq [policy [{"workspace" origin} false []]]
            (let [error (caught #(ygg/copy-fork! handle 2 {:checkpoints policy :admit (fn [_] (swap! admissions inc))}))]
              (is (= ::ygg/checkpoint-copy-policy (:type (ex-data error))))
              (is (ygg/open-fork? handle))
              (is (= before (d/branches conn)))
              (is (zero? @admissions))))
          (let [copies (ygg/copy-fork! handle 2)]
            (try
              (doseq [copy copies]
                (ygg/with-fork copy
                  (let [selected (gy/connection (ygg/system "workspace"))]
                    (is (= "C1" (text selected "state.md")))
                    (is (= "Current edits" (text selected "proposal.md"))))))
              (finally (doseq [copy copies] (ygg/discard-fork! copy)))))
          (is (= "C2" (text conn "state.md")))
          (is (nil? (text conn "proposal.md"))))))))

(deftest scoped-checkpoints-belong-to-one-fork-and-cannot-be-reusable-defaults
  (with-repo
    (fn [conn]
      (commit! conn "state.md" "C1")
      (let [origin (checkpoint conn) before (d/branches conn)]
        (doseq [policy [{"workspace" origin} false []]]
          (is (= ::scope/checkpoint-scope-defaults
                 (:type (ex-data (caught #(scope/create {:fork-opts {:checkpoints policy}}))))))
          (is (= before (d/branches conn))))
        (commit! conn "state.md" "C2")
        (let [parent ec/*execution-context* world-scope (scope/create {})
              activity (scope/begin-activity! world-scope :checkpoint-fixture)
              first-world (await-cps #(scope/fork! world-scope parent {:fork-opts {:checkpoints {"workspace" origin}}} %1 %2))
              next-world (await-cps #(scope/fork! world-scope parent %1 %2))]
          (try
            (binding [ec/*execution-context* (:child-ctx first-world)]
              (is (= "C1" (text (gy/connection (ygg/system "workspace")) "state.md"))))
            (binding [ec/*execution-context* (:child-ctx next-world)]
              (is (= "C2" (text (gy/connection (ygg/system "workspace")) "state.md"))))
            (is (nil? (get-in @world-scope [:fork-opts :checkpoints])))
            (is (nil? (get-in (:child-ctx first-world) [:bindings :checkpoints])))
            (finally (scope/end-activity! world-scope activity)
                     (await-cps (scope/discard! world-scope)))))))))

(deftest asynchronous-run-admission-uses-the-same-owned-checkpoint-workspace
  (with-repo
    (fn [conn]
      (commit! conn "state.md" "C1")
      (let [origin (checkpoint conn)]
        (commit! conn "state.md" "C2")
        (let [branches (d/branches conn)
              handle (await-cps (ygg/fork! {:sync? false :checkpoints {"workspace" origin}}))]
          (try
            (ygg/with-fork handle
              (is (= "C1" (text (gy/connection (ygg/system "workspace")) "state.md"))))
            (is (= "C2" (text conn "state.md")))
            (finally (await-cps (ygg/discard-fork! handle {:sync? false}))))
          (is (= branches (d/branches conn))))))))
