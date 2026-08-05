(ns org.replikativ.spindel.dom.commit-reconcile-test
  "Unit tests for commit-time reconciliation (dom/commit) — the property the
   compute-time path cannot have.

   THE property: N distinct builds of the same state, committed in sequence,
   produce the DOM change ONCE. Under compute-time reconciliation every build
   diffs against the same uncommitted baseline and carries the same `:add`;
   here the first commit advances the baseline in the same step as the DOM
   write, so every later build — a DIFFERENT object, which no identity-keyed
   guard can catch — diffs to nothing. This is the N-builds window measured
   live in simmis (six builds of one container per settled expand, the same
   `:add` discharged in two passes; see jsdom_final_state_test.cljs, the
   deliberately-failing acceptance test).

   These tests drive `commit-reconcile!` directly against `MockDischarge`
   with hand-built vnodes carrying explicit `:slots` — no engine, no spins,
   no timing. Op-count assertions only (creates/inserts/removes/set-attrs):
   the earlier replay-the-log-into-a-tree metric was measured unsound
   (repeat_execution_test.clj records why), but op counts on a SINGLE
   ADDRESS with single-digit expectations are exactly what the mock can
   answer."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.dom.commit :as commit]
            [org.replikativ.spindel.dom.cache :as cache]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.incremental.sequence-algebra :as sa]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]))

(defn clean-context-fixture [f]
  (binding [ec/*execution-context* nil]
    (f)))

(use-fixtures :each clean-context-fixture)

;; =============================================================================
;; Construction helpers — explicit :slots, the carrier the commit walk needs
;; =============================================================================

(defn- vn
  "A vnode with explicit slot structure. `:children` derived by flattening,
   as build-element does."
  [tag addr attrs & slot-values]
  (let [slots (mapv cache/make-slot slot-values)]
    {:tag tag :addr addr :attrs attrs
     :slots slots
     :children (cache/flatten-slots slots)}))

(defn- text [s] {:tag :text :content s})

(defn- ops [log & kinds]
  (let [ks (set kinds)]
    (count (filter #(ks (:op %)) @log))))

(defn- mount!
  "Initial mount as production does it: render + seed caches. Returns the log."
  [discharge root]
  (disch/render-initial! discharge root)
  (commit/seed-subtree-caches! root))

;; =============================================================================
;; 0. The keyed unit property (the de-risk probe from the evaluation)
;; =============================================================================

(deftest keyed-diff-against-advanced-baseline-is-nil
  (testing "keyed-seq-diff twice against ONE baseline grows twice; against
            the ADVANCED baseline it is nil — the keyed analogue of
            repeat_execution_test's attr/child property"
    (let [prev-order []
          prev-by-key {}
          item {:tag :li :addr :el-item-a :key "a" :attrs {} :children []}
          order ["a"]
          by-key {"a" item}
          d1 (sa/keyed-seq-diff order prev-order by-key prev-by-key
                                foreach/vnode-value-equal?)
          d2 (sa/keyed-seq-diff order prev-order by-key prev-by-key
                                foreach/vnode-value-equal?)]
      (is (= 1 (:grow d1)))
      (is (= 1 (:grow d2)) "unadvanced baseline re-grows — the duplication")
      (is (nil? (sa/keyed-seq-diff order order by-key by-key
                                   foreach/vnode-value-equal?))
          "advanced baseline: no diff"))))

;; =============================================================================
;; 1. THE property: N distinct builds, one insert
;; =============================================================================

(deftest n-builds-one-insert
  (testing "a conditional child appears; five distinct builds of the new
            state committed in sequence insert it exactly once"
    (with-ctx [_rt]
      (let [{:keys [discharge log]} (disch/make-mock-discharge)
            base (vn :div :el-shell {:class "shell"} nil (text "static"))
            ;; five DISTINCT builds of the expanded state — distinct objects,
            ;; equal content: exactly what the N-builds window produces and
            ;; what identity-keyed guards cannot catch
            build (fn [] (vn :div :el-shell {:class "shell"}
                             (vn :ul :el-items {:class "items"} (text "one"))
                             (text "static")))]
        (mount! discharge base)
        (reset! log [])
        (dotimes [_ 5]
          (commit/commit-reconcile! discharge (build)))
        (is (= 1 (ops log :create-element))
            "the <ul> is created once across five commits")
        ;; :insert-child only — the ul's own text child arrives via
        ;; :append-child inside its render-initial!, which is part of the ONE
        ;; legitimate creation, not a second slot-level insert
        (is (= 1 (ops log :insert-child))
            (str "one slot-level insert, got ops: " (vec @log)))))))

(deftest stale-build-after-removal-does-not-resurrect
  (testing "expand build replayed AFTER the collapse committed: the stale
            :add diffs against the advanced (collapsed) baseline as a
            legitimate re-add — but a collapse build replayed after expand
            removes once, not twice (no live-sibling deletion)"
    (with-ctx [_rt]
      (let [{:keys [discharge log]} (disch/make-mock-discharge)
            collapsed (fn [] (vn :div :el-shell {:class "shell"} nil (text "s")))
            expanded  (fn [] (vn :div :el-shell {:class "shell"}
                                 (vn :ul :el-items {:class "items"} (text "one"))
                                 (text "s")))]
        (mount! discharge (expanded))
        (reset! log [])
        ;; collapse committed once, then the SAME collapse state committed
        ;; again from a distinct stale build
        (commit/commit-reconcile! discharge (collapsed))
        (commit/commit-reconcile! discharge (collapsed))
        (is (= 1 (ops log :remove-child))
            (str "exactly one removal — a second one would delete the live "
                 "text sibling at that index; got " (vec @log)))))))

(deftest attrs-advance-with-the-write
  (testing "an attr change applies once across distinct builds; a genuinely
            newer build still applies its residual"
    (with-ctx [_rt]
      (let [{:keys [discharge log]} (disch/make-mock-discharge)
            v (fn [cls] (vn :div :el-shell {:class cls} (text "s")))]
        (mount! discharge (v "a"))
        (reset! log [])
        (commit/commit-reconcile! discharge (v "b"))
        (commit/commit-reconcile! discharge (v "b"))   ; stale duplicate
        (is (= 1 (ops log :set-attr)) "one write for two b-builds")
        (commit/commit-reconcile! discharge (v "c"))   ; genuinely newer
        (is (= 2 (ops log :set-attr)) "the residual of a newer build applies")))))

;; =============================================================================
;; 2. The keyed path: fragment growth commits once
;; =============================================================================

(defn- li [k]
  {:tag :li :addr (keyword (str "el-li-" k)) :key k
   :attrs {} :slots [(cache/make-slot (text k))] :children [(text k)]})

(defn- shell-with-frag
  "Shell whose single slot is a KeyedFragment of `ks`."
  [ks]
  (let [items (mapv li ks)
        fragment (assoc (frag/keyed-fragment items nil) :addr :el-frag)]
    {:tag :div :addr :el-shell :attrs {:class "shell"}
     :slots [(cache/make-slot fragment)]
     :children (vec items)}))

(deftest fragment-growth-commits-once
  (testing "an item appears in the fragment; three distinct builds insert it
            once — the .sub-items duplication of the acceptance test, at
            unit scale"
    (with-ctx [_rt]
      (let [{:keys [discharge log]} (disch/make-mock-discharge)]
        (mount! discharge (shell-with-frag ["a" "b"]))
        (reset! log [])
        (dotimes [_ 3]
          (commit/commit-reconcile! discharge (shell-with-frag ["a" "b" "c"])))
        (is (= 1 (ops log :create-element))
            (str "the new <li> is created once, got " (vec @log)))))))

(deftest nested-conditional-inside-fragment-item-commits-once
  (testing "the app shape at unit scale: a fragment item's OWN conditional
            child appears; repeated commits of distinct builds insert the
            nested container once (recursion into surviving keyed items)"
    (with-ctx [_rt]
      (let [{:keys [discharge log]} (disch/make-mock-discharge)
            item (fn [open?]
                   (let [slots [(cache/make-slot (text "hd"))
                                (cache/make-slot
                                 (when open?
                                   (vn :ul :el-sub {:class "sub"} (text "p"))))]]
                     {:tag :div :addr :el-item-a :key "a" :attrs {}
                      :slots slots :children (cache/flatten-slots slots)}))
            shell (fn [open?]
                    (let [fragment (assoc (frag/keyed-fragment [(item open?)] nil)
                                          :addr :el-frag)]
                      {:tag :div :addr :el-shell :attrs {}
                       :slots [(cache/make-slot fragment)]
                       :children [(item open?)]}))]
        (mount! discharge (shell false))
        (reset! log [])
        (dotimes [_ 4]
          (commit/commit-reconcile! discharge (shell true)))
        (is (= 1 (ops log :create-element))
            (str "the nested <ul> is created once across four distinct "
                 "builds, got " (vec @log)))))))
