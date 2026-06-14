(ns org.replikativ.spindel.yggdrasil-test
  "Tests for yggdrasil integration with spindel execution contexts.

   CLJ-only: Requires git filesystem operations."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.test-helpers :as th]
            [yggdrasil.adapters.git :as git-adapter]
            [yggdrasil.protocols :as ygg-proto]
            [clojure.java.io :as io]
            [clojure.java.shell :refer [sh]]))

;; =============================================================================
;; Test Fixtures - Temporary Git Repository
;; =============================================================================

(def ^:dynamic *test-repo-path* nil)
(def ^:dynamic *test-git-system* nil)

(defn create-temp-repo
  "Create a temporary git repository for testing."
  []
  (let [temp-dir (io/file (System/getProperty "java.io.tmpdir")
                          (str "spindel-ygg-test-" (System/currentTimeMillis)))
        path (.getAbsolutePath temp-dir)]
    (.mkdirs temp-dir)
    ;; Initialize git repo
    (sh "git" "init" "--initial-branch=main" :dir path)
    (sh "git" "config" "user.email" "test@spindel.is" :dir path)
    (sh "git" "config" "user.name" "Spindel Test" :dir path)
    ;; Create initial commit so we have a valid HEAD
    (spit (io/file path "README.md") "# Test Repo")
    (sh "git" "add" "README.md" :dir path)
    (sh "git" "commit" "-m" "Initial commit" :dir path)
    path))

(defn cleanup-temp-repo
  "Remove temporary git repository and its worktrees."
  [path]
  (when path
    (let [worktrees-dir (str path "-worktrees")]
      ;; Remove worktrees directory first
      (when (.exists (io/file worktrees-dir))
        (sh "rm" "-rf" worktrees-dir))
      ;; Remove main repo
      (sh "rm" "-rf" path))))

(defn with-temp-repo
  "Fixture that creates and cleans up a temporary git repo."
  [f]
  (let [repo-path (create-temp-repo)]
    (try
      (binding [*test-repo-path* repo-path
                *test-git-system* (git-adapter/create repo-path)]
        (f))
      (finally
        (cleanup-temp-repo repo-path)))))

(use-fixtures :each with-temp-repo)

;; =============================================================================
;; YggRef Basic Tests
;; =============================================================================

(deftest test-yggref-creation
  (testing "YggRef can be created and dereferenced"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)]
        (is (ygg/ygg-ref? yref) "register! returns a YggRef")
        (is (some? @yref) "YggRef can be dereferenced")
        (is (= :main (ygg-proto/current-branch @yref))
            "Dereferenced system is on main branch")))))

(deftest test-yggref-outside-context-throws
  (testing "YggRef deref outside context throws meaningful error"
    (let [ctx (ctx/create-execution-context)]
      (try
        (let [yref (binding [ec/*execution-context* ctx]
                     (ygg/register! *test-git-system*))]
          ;; Outside the context, deref should throw
          (let [ctx-empty (ctx/create-execution-context)]
            (try
              (binding [ec/*execution-context* ctx-empty]
                (is (thrown-with-msg? clojure.lang.ExceptionInfo
                                      #"Yggdrasil system not found"
                                      @yref)))
              (finally
                (ctx/stop-context! ctx-empty)))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-registered-systems
  (testing "registered-systems returns all registered systems"
    (th/with-ctx [ctx]
      (is (empty? (ygg/registered-systems)) "Initially empty")
      (ygg/register! *test-git-system*)
      (is (= 1 (count (ygg/registered-systems))) "One system registered"))))

;; =============================================================================
;; Fork Basic Tests
;; =============================================================================

(deftest test-fork-creates-branch
  (testing "fork! creates a new git branch"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            _ (is (= :main (ygg-proto/current-branch @yref)))
            fork-handle (ygg/fork!)]

        ;; Parent should still be on main
        (is (= :main (ygg-proto/current-branch @yref))
            "Parent stays on main after fork")

        ;; Inside fork, should be on forked branch
        (ygg/with-fork fork-handle
          (let [forked-branch (ygg-proto/current-branch @yref)]
            (is (not= :main forked-branch)
                "Fork is on different branch")
            (is (clojure.string/starts-with? (name forked-branch) "overlay-")
                "Forked branch is the overlay fork branch (overlay-<uuid>)")))

        ;; Cleanup
        (ygg/discard-fork! fork-handle)))))

(deftest test-fork-isolation
  (testing "Parent and fork have independent git systems"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            fork-handle (ygg/fork!)
            parent-identity (System/identityHashCode @yref)]

        (ygg/with-fork fork-handle
          (let [fork-identity (System/identityHashCode @yref)]
            (is (not= parent-identity fork-identity)
                "Fork has different system instance")))

        (ygg/discard-fork! fork-handle)))))

(deftest test-fork-worktree-exists
  (testing "Fork creates worktree directory"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            fork-handle (ygg/fork!)]

        (ygg/with-fork fork-handle
          (let [branch-name (name (ygg-proto/current-branch @yref))
                worktrees-dir (:worktrees-dir @yref)
                wt-path (str worktrees-dir "/" branch-name)]
            (is (.exists (io/file wt-path))
                "Worktree directory exists")))

        (ygg/discard-fork! fork-handle)))))

;; =============================================================================
;; Merge Tests
;; =============================================================================

(deftest test-merge-fork
  (testing "merge-fork! merges forked branch to parent"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            fork-handle (ygg/fork!)]

        ;; Make a change in the fork
        (ygg/with-fork fork-handle
          (let [branch-name (name (ygg-proto/current-branch @yref))
                worktrees-dir (:worktrees-dir @yref)
                wt-path (str worktrees-dir "/" branch-name)
                test-file (str wt-path "/fork-test.txt")]
            (spit test-file "Created in fork")
            (sh "git" "add" "fork-test.txt" :dir wt-path)
            (sh "git" "commit" "-m" "Fork commit" :dir wt-path)))

        ;; Merge should succeed
        (ygg/merge-fork! fork-handle)

        ;; After merge, parent should have the file
        (let [repo-path (:repo-path @yref)
              merged-file (str repo-path "/fork-test.txt")]
          (is (.exists (io/file merged-file))
              "Merged file exists in parent"))))))

(deftest test-discard-fork-cleanup
  (testing "discard-fork! removes forked branch and worktree"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            fork-handle (ygg/fork!)
            forked-branch-name (atom nil)
            forked-wt-path (atom nil)]

        ;; Capture fork info
        (ygg/with-fork fork-handle
          (reset! forked-branch-name (name (ygg-proto/current-branch @yref)))
          (let [worktrees-dir (:worktrees-dir @yref)]
            (reset! forked-wt-path (str worktrees-dir "/" @forked-branch-name))))

        ;; Verify worktree exists before discard
        (is (.exists (io/file @forked-wt-path))
            "Worktree exists before discard")

        ;; Discard
        (ygg/discard-fork! fork-handle)

        ;; Worktree should be gone
        (is (not (.exists (io/file @forked-wt-path)))
            "Worktree removed after discard")

        ;; Branch should be gone
        (let [branches (ygg-proto/branches @yref)]
          (is (not (contains? branches (keyword @forked-branch-name)))
              "Branch removed after discard"))))))

;; =============================================================================
;; Child-only systems on merge / discard + lifecycle callbacks
;; =============================================================================

(deftest test-merge-carries-child-only-system
  (testing "a system registered ONLY in the fork is carried to the parent on merge, and :on-merge fires"
    (th/with-ctx [ctx]
      (ygg/register! *test-git-system*)                 ; base system, in the parent
      (let [fork-handle (ygg/fork!)
            child-repo  (create-temp-repo)
            cb          (atom nil)]
        ;; register a NEW system that exists ONLY in the fork
        (ygg/with-fork fork-handle
          (ygg/register! (git-adapter/create child-repo {:system-name "child-only"})))
        (is (nil? (ygg/system "child-only")) "fork-only system is invisible in the parent before merge")
        (ygg/merge-fork! fork-handle {:on-merge (fn [m] (reset! cb m))})
        (is (some? (ygg/system "child-only")) "fork-only system is CARRIED into the parent on merge")
        (is (= ["child-only"] (mapv str (:child-only @cb))) ":on-merge callback received the child-only set")
        (cleanup-temp-repo child-repo)))))

(deftest test-discard-fires-on-discard-with-child-only
  (testing "discard fires :on-discard with the fork-only systems so an external owner can clean up"
    (th/with-ctx [ctx]
      (ygg/register! *test-git-system*)
      (let [fork-handle (ygg/fork!)
            child-repo  (create-temp-repo)
            cb          (atom nil)]
        (ygg/with-fork fork-handle
          (ygg/register! (git-adapter/create child-repo {:system-name "scratch"})))
        (ygg/discard-fork! fork-handle {:on-discard (fn [m] (reset! cb m))})
        (is (= ["scratch"] (mapv str (:child-only @cb))) ":on-discard callback received the child-only set")
        (is (nil? (ygg/system "scratch")) "fork-only system is not in the parent after discard")
        (cleanup-temp-repo child-repo)))))

;; =============================================================================
;; Nested Fork Tests
;; =============================================================================

(deftest test-nested-forks
  (testing "Forks can be nested (fork from fork)"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            outer-fork (ygg/fork!)]

        (ygg/with-fork outer-fork
          (let [outer-branch (ygg-proto/current-branch @yref)
                inner-fork (ygg/fork!)]

            (ygg/with-fork inner-fork
              (let [inner-branch (ygg-proto/current-branch @yref)]
                (is (not= outer-branch inner-branch)
                    "Inner fork has different branch than outer")
                (is (clojure.string/starts-with? (name inner-branch) "overlay-")
                    "Inner fork is its own overlay branch (overlay-<uuid>)")))

            (ygg/discard-fork! inner-fork)))

        (ygg/discard-fork! outer-fork)))))

;; =============================================================================
;; Snapshot Fork Tests (pin a FIXED value — "fix a value, run in isolation")
;; =============================================================================

(deftest test-snapshot-fork-pins-fixed-value
  (testing "fork! with :snapshots pins a system at a FIXED snapshot-id — the fork
            sees the frozen past value, NOT the parent's later advance"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            sid  (ygg-proto/system-id *test-git-system*)
            repo (:repo-path @yref)]
        ;; state-1: commit a file, capture the snapshot-id
        (spit (str repo "/v1.txt") "one")
        (sh "git" "add" "v1.txt" :dir repo)
        (sh "git" "commit" "-m" "v1" :dir repo)
        (let [snap1 (ygg-proto/snapshot-id @yref)]
          ;; state-2: advance the PARENT past the captured snapshot
          (spit (str repo "/v2.txt") "two")
          (sh "git" "add" "v2.txt" :dir repo)
          (sh "git" "commit" "-m" "v2" :dir repo)
          ;; snapshot-fork pinned at state-1
          (let [fork-handle (ygg/fork! {:snapshots {sid snap1}})]
            (ygg/with-fork fork-handle
              (let [branch (name (ygg-proto/current-branch @yref))
                    wt     (str (:worktrees-dir @yref) "/" branch)]
                (is (clojure.string/starts-with? branch "snap-")
                    "snapshot fork is on a snap-<fork> branch")
                (is (.exists (io/file (str wt "/v1.txt")))
                    "the pinned state-1 file is present in the fork")
                (is (not (.exists (io/file (str wt "/v2.txt"))))
                    "the parent's later state-2 is NOT present (frozen at the snapshot)")))))))))

;; =============================================================================
;; ForkHandle Tests
;; =============================================================================

(deftest test-fork-handle-type
  (testing "fork! returns a ForkHandle"
    (th/with-ctx [ctx]
      (ygg/register! *test-git-system*)
      (let [fork-handle (ygg/fork!)]
        (is (ygg/fork-handle? fork-handle)
            "fork! returns ForkHandle")
        (is (:child-ctx fork-handle)
            "ForkHandle has child-ctx")
        (is (:parent-ctx fork-handle)
            "ForkHandle has parent-ctx")
        (is (:fork-id fork-handle)
            "ForkHandle has fork-id")
        (ygg/discard-fork! fork-handle)))))

;; =============================================================================
;; Merge From Parent Tests
;; =============================================================================

(deftest test-merge-from-parent
  (testing "merge-from-parent! pulls parent changes into child"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            fork-handle (ygg/fork!)
            child-ctx (:child-ctx fork-handle)]

        ;; Make a change in the parent (simulates another agent's merged work)
        (let [repo-path (:repo-path @yref)
              parent-file (str repo-path "/parent-change.txt")]
          (spit parent-file "Added by parent after fork")
          (sh "git" "add" "parent-change.txt" :dir repo-path)
          (sh "git" "commit" "-m" "Parent commit after fork" :dir repo-path))

        ;; Before merge, child should NOT have the parent file
        (ygg/with-fork fork-handle
          (let [branch-name (name (ygg-proto/current-branch @yref))
                worktrees-dir (:worktrees-dir @yref)
                wt-path (str worktrees-dir "/" branch-name)]
            (is (not (.exists (io/file (str wt-path "/parent-change.txt"))))
                "Child does NOT have parent's file before merge")))

        ;; Merge: pull parent's changes into child
        (ygg/merge-from-parent! child-ctx)

        ;; After merge, child SHOULD have the parent file
        (ygg/with-fork fork-handle
          (let [branch-name (name (ygg-proto/current-branch @yref))
                worktrees-dir (:worktrees-dir @yref)
                wt-path (str worktrees-dir "/" branch-name)]
            (is (.exists (io/file (str wt-path "/parent-change.txt")))
                "Child HAS parent's file after merge")))

        (ygg/discard-fork! fork-handle)))))

(deftest test-merge-from-parent-preserves-child-work
  (testing "merge-from-parent! preserves child's own changes"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            fork-handle (ygg/fork!)
            child-ctx (:child-ctx fork-handle)]

        ;; Make a change in the fork first
        (ygg/with-fork fork-handle
          (let [branch-name (name (ygg-proto/current-branch @yref))
                worktrees-dir (:worktrees-dir @yref)
                wt-path (str worktrees-dir "/" branch-name)
                child-file (str wt-path "/child-work.txt")]
            (spit child-file "Work done in child")
            (sh "git" "add" "child-work.txt" :dir wt-path)
            (sh "git" "commit" "-m" "Child commit" :dir wt-path)))

        ;; Make a change in the parent
        (let [repo-path (:repo-path @yref)
              parent-file (str repo-path "/parent-update.txt")]
          (spit parent-file "Parent update")
          (sh "git" "add" "parent-update.txt" :dir repo-path)
          (sh "git" "commit" "-m" "Parent update" :dir repo-path))

        ;; Merge from parent
        (ygg/merge-from-parent! child-ctx)

        ;; After merge, child should have BOTH files
        (ygg/with-fork fork-handle
          (let [branch-name (name (ygg-proto/current-branch @yref))
                worktrees-dir (:worktrees-dir @yref)
                wt-path (str worktrees-dir "/" branch-name)]
            (is (.exists (io/file (str wt-path "/child-work.txt")))
                "Child's own work preserved after merge")
            (is (.exists (io/file (str wt-path "/parent-update.txt")))
                "Parent's update pulled in after merge")))

        (ygg/discard-fork! fork-handle)))))

(deftest test-merge-fork-from-parent
  (testing "merge-fork-from-parent! works with ForkHandle"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            fork-handle (ygg/fork!)]

        ;; Add file in parent
        (let [repo-path (:repo-path @yref)]
          (spit (str repo-path "/via-handle.txt") "handle test")
          (sh "git" "add" "via-handle.txt" :dir repo-path)
          (sh "git" "commit" "-m" "For handle test" :dir repo-path))

        ;; Merge from parent via fork handle
        (ygg/merge-fork-from-parent! fork-handle)

        ;; Verify
        (ygg/with-fork fork-handle
          (let [branch-name (name (ygg-proto/current-branch @yref))
                worktrees-dir (:worktrees-dir @yref)
                wt-path (str worktrees-dir "/" branch-name)]
            (is (.exists (io/file (str wt-path "/via-handle.txt")))
                "File present after merge-fork-from-parent!")))

        (ygg/discard-fork! fork-handle)))))

;; =============================================================================
;; Multiple Systems Tests
;; =============================================================================

(deftest test-multiple-systems-fork
  (testing "Multiple registered systems are all forked"
    (let [ctx (ctx/create-execution-context)
          ;; Create a second temp repo
          second-repo-path (create-temp-repo)
          second-git-system (git-adapter/create second-repo-path)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [yref1 (ygg/register! *test-git-system*)
                yref2 (ygg/register! second-git-system)
                fork-handle (ygg/fork!)]

            ;; Both should be forked
            (ygg/with-fork fork-handle
              (is (not= :main (ygg-proto/current-branch @yref1))
                  "First system is forked")
              (is (not= :main (ygg-proto/current-branch @yref2))
                  "Second system is forked"))

            (ygg/discard-fork! fork-handle)))
        (finally
          (ctx/stop-context! ctx)
          (cleanup-temp-repo second-repo-path))))))

;; =============================================================================
;; Registry / per-signal API Tests
;; =============================================================================

(deftest test-register-creates-ygg-signal
  (testing "register! creates a resolvable ygg-signal per system — no privileged workspace"
    (th/with-ctx [ctx]
      (is (empty? (ygg/registered-systems)) "Nothing registered before register!")
      (ygg/register! *test-git-system*)
      (let [sid (ygg-proto/system-id *test-git-system*)]
        (is (some? (ygg/system-signal sid)) "a ygg-signal holds the system")
        (is (= :git (ygg-proto/system-type (ygg/system sid))) "system resolves to the git system")
        (is (= 1 (count (ygg/registered-systems))) "one registered system")))))

(deftest test-system-resolution
  (testing "system / get-system resolve the effective system; @yref agrees"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            sid  (ygg-proto/system-id *test-git-system*)]
        (is (identical? @yref (ygg/system sid))
            "ygg/system returns the same instance as @yref (root: no overlay)")
        (is (= :git (ygg-proto/system-type (ygg/system sid))))))))

(deftest test-workspace-diff-merge-base
  (testing "workspace-diff reports the fork's OWN change via per-system merge-base"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            sid  (ygg-proto/system-id *test-git-system*)
            fork-handle (ygg/fork!)
            child-ctx (:child-ctx fork-handle)]
        ;; Commit a file inside the fork
        (ygg/with-fork fork-handle
          (let [branch-name (name (ygg-proto/current-branch @yref))
                wt-path (str (:worktrees-dir @yref) "/" branch-name)]
            (spit (str wt-path "/ws-diff.txt") "fork change")
            (sh "git" "add" "ws-diff.txt" :dir wt-path)
            (sh "git" "commit" "-m" "ws diff commit" :dir wt-path)))
        ;; Advance the PARENT independently — merge-base must exclude this
        (let [repo-path (:repo-path @yref)]
          (spit (str repo-path "/parent-only.txt") "parent advance")
          (sh "git" "add" "parent-only.txt" :dir repo-path)
          (sh "git" "commit" "-m" "parent advance" :dir repo-path))
        (let [diff (ygg/workspace-diff child-ctx)
              gdiff (get diff sid)
              files (set (map :path (:files gdiff)))]
          (is (some? gdiff) "workspace-diff has the git sub-system")
          (is (contains? files "ws-diff.txt") "fork's own file is in the diff")
          (is (not (contains? files "parent-only.txt"))
              "parent's concurrent advance is excluded (merge-base)"))
        (ygg/discard-fork! fork-handle)))))

(deftest test-workspace-merge-transactional
  (testing "merge-to-parent! returns :merged and lands the fork's change"
    (th/with-ctx [ctx]
      (let [yref (ygg/register! *test-git-system*)
            sid  (ygg-proto/system-id *test-git-system*)
            fork-handle (ygg/fork!)
            child-ctx (:child-ctx fork-handle)]
        (ygg/with-fork fork-handle
          (let [branch-name (name (ygg-proto/current-branch @yref))
                wt-path (str (:worktrees-dir @yref) "/" branch-name)]
            (spit (str wt-path "/ws-merge.txt") "merge me")
            (sh "git" "add" "ws-merge.txt" :dir wt-path)
            (sh "git" "commit" "-m" "ws merge commit" :dir wt-path)))
        (let [result (ygg/merge-to-parent! child-ctx)]
          (is (contains? (set (:merged result)) sid)
              "merge-to-parent! reports the merged sub-system")
          (is (.exists (io/file (str (:repo-path @yref) "/ws-merge.txt")))
              "fork's file landed in the parent"))))))
