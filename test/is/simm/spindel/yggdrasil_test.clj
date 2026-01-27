(ns is.simm.spindel.yggdrasil-test
  "Tests for yggdrasil integration with spindel execution contexts.

   CLJ-only: Requires git filesystem operations."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [is.simm.spindel.yggdrasil :as ygg]
            [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.runtime.context :as ctx]
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
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [yref (ygg/register! *test-git-system*)]
          (is (ygg/ygg-ref? yref) "register! returns a YggRef")
          (is (some? @yref) "YggRef can be dereferenced")
          (is (= :main (ygg-proto/current-branch @yref))
              "Dereferenced system is on main branch"))))))

(deftest test-yggref-outside-context-throws
  (testing "YggRef deref outside context throws meaningful error"
    (let [ctx (ctx/create-execution-context)
          yref (binding [rtc/*execution-context* ctx]
                 (ygg/register! *test-git-system*))]
      ;; Outside the context, deref should throw
      (let [ctx-empty (ctx/create-execution-context)]
        (binding [rtc/*execution-context* ctx-empty]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo
                                #"Yggdrasil system not found"
                                @yref)))))))

(deftest test-registered-systems
  (testing "registered-systems returns all registered systems"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (is (empty? (ygg/registered-systems)) "Initially empty")
        (ygg/register! *test-git-system*)
        (is (= 1 (count (ygg/registered-systems))) "One system registered")))))

;; =============================================================================
;; Fork Basic Tests
;; =============================================================================

(deftest test-fork-creates-branch
  (testing "fork! creates a new git branch"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
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
              (is (clojure.string/starts-with? (name forked-branch) "main-fork-")
                  "Forked branch name follows convention (main-fork-<uuid>)")))

          ;; Cleanup
          (ygg/discard-fork! fork-handle))))))

(deftest test-fork-isolation
  (testing "Parent and fork have independent git systems"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [yref (ygg/register! *test-git-system*)
              fork-handle (ygg/fork!)
              parent-identity (System/identityHashCode @yref)]

          (ygg/with-fork fork-handle
            (let [fork-identity (System/identityHashCode @yref)]
              (is (not= parent-identity fork-identity)
                  "Fork has different system instance")))

          (ygg/discard-fork! fork-handle))))))

(deftest test-fork-worktree-exists
  (testing "Fork creates worktree directory"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [yref (ygg/register! *test-git-system*)
              fork-handle (ygg/fork!)]

          (ygg/with-fork fork-handle
            (let [branch-name (name (ygg-proto/current-branch @yref))
                  worktrees-dir (:worktrees-dir @yref)
                  wt-path (str worktrees-dir "/" branch-name)]
              (is (.exists (io/file wt-path))
                  "Worktree directory exists")))

          (ygg/discard-fork! fork-handle))))))

;; =============================================================================
;; Merge Tests
;; =============================================================================

(deftest test-merge-fork
  (testing "merge-fork! merges forked branch to parent"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
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
                "Merged file exists in parent")))))))

(deftest test-discard-fork-cleanup
  (testing "discard-fork! removes forked branch and worktree"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
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
                "Branch removed after discard")))))))

;; =============================================================================
;; Nested Fork Tests
;; =============================================================================

(deftest test-nested-forks
  (testing "Forks can be nested (fork from fork)"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [yref (ygg/register! *test-git-system*)
              outer-fork (ygg/fork!)]

          (ygg/with-fork outer-fork
            (let [outer-branch (ygg-proto/current-branch @yref)
                  inner-fork (ygg/fork!)]

              (ygg/with-fork inner-fork
                (let [inner-branch (ygg-proto/current-branch @yref)]
                  (is (not= outer-branch inner-branch)
                      "Inner fork has different branch than outer")
                  (is (clojure.string/starts-with? (name inner-branch)
                                                   (name outer-branch))
                      "Inner branch name derives from outer")))

              (ygg/discard-fork! inner-fork)))

          (ygg/discard-fork! outer-fork))))))

;; =============================================================================
;; ForkHandle Tests
;; =============================================================================

(deftest test-fork-handle-type
  (testing "fork! returns a ForkHandle"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
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
          (ygg/discard-fork! fork-handle))))))

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
        (binding [rtc/*execution-context* ctx]
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
          (cleanup-temp-repo second-repo-path))))))
