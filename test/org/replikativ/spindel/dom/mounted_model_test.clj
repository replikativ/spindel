(ns org.replikativ.spindel.dom.mounted-model-test
  "The mounted model is the committed tree; unmount is the DIFFERENCE
   between two successive committed trees — one owner, one derivation
   (`commit/retire-dead!`).

   This replaces the deferred-eviction choreography (*pending-evictions* /
   flush-pending-evictions! / the keyed-cache cascade and its liveness
   closure), which synchronized three parallel owners of \"what is
   mounted\" by convention and drifted (measured: an element removed while
   its parent's committed slots still claimed it — a permanently frozen
   subtree warning ::commit-unbound-addr). Between two committed trees
   there is no mid-walk ambiguity: an address is in the new tree or it is
   not. The properties the old machinery guarded now hold structurally:

   - A->B->A / churned-parent-surviving-child: a re-claimed address is in
     the new tree, hence never in the dead set — spared by construction.
   - The ifor-each keyed-cache leak: a dead fragment's call-site address
     is in `tree-addrs` directly (read off :slots), no cascade needed.
   - The PR#39 live-fragment eviction bug: a LIVE fragment is in the new
     tree, hence never dead."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.dom.commit :as commit]
            [org.replikativ.spindel.dom.cache :as cache]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]))

(defn- vn [tag addr & slot-values]
  (let [slots (mapv cache/make-slot slot-values)]
    {:tag tag :addr addr :attrs {}
     :slots slots :children (cache/flatten-slots slots)}))

(defn- li [k]
  {:tag :li :addr (keyword (str "el-li-" k)) :key k :attrs {}
   :slots [] :children []})

(deftest tree-addrs-is-the-mounted-model
  (testing "element addrs + fragment call sites + keyed items; :nil slots
            contribute nothing"
    (let [fragment (assoc (frag/keyed-fragment [(li "a") (li "b")] nil)
                          :addr :el-frag)
          tree (vn :div :el-root
                   (vn :span :el-child)
                   nil                      ; a :nil conditional slot
                   fragment)]
      (is (= #{:el-root :el-child :el-frag :el-li-a :el-li-b}
             (commit/tree-addrs tree))))))

(deftest retire-dead-is-the-tree-difference
  (testing "prev-minus-new addresses lose caches and registry entries;
            addresses in both trees are untouched"
    (with-ctx [_ctx]
      (let [{:keys [discharge elements]} (disch/make-mock-discharge)
            prev (vn :div :el-root (vn :span :el-keep) (vn :ul :el-gone))
            new' (vn :div :el-root (vn :span :el-keep) nil)]
        (doseq [a [:el-root :el-keep :el-gone]]
          (cache/set-slot-cache! a [])
          (disch/set-element! discharge a (keyword (str "node-" (name a)))))
        (commit/retire-dead! discharge prev new')
        (is (nil? (cache/get-slot-cache :el-gone)) "dead addr evicted")
        (is (nil? (get @elements :el-gone)) "dead addr out of the registry")
        (is (some? (cache/get-slot-cache :el-keep)) "surviving addr spared")
        (is (= :node-el-keep (get @elements :el-keep))
            "surviving registry entry spared")
        (is (some? (cache/get-slot-cache :el-root)))))))

(deftest reclaimed-address-is-never-dead
  (testing "the A->B->A case the deferred machinery existed for: an address
            present in BOTH trees — even under a different parent — is not
            in the difference, so nothing can evict it"
    (with-ctx [_ctx]
      (let [{:keys [discharge]} (disch/make-mock-discharge)
            prev (vn :div :el-root (vn :section :el-old-parent (vn :p :el-moved)))
            new' (vn :div :el-root (vn :article :el-new-parent (vn :p :el-moved)))]
        (cache/set-slot-cache! :el-moved [])
        (commit/retire-dead! discharge prev new')
        (is (some? (cache/get-slot-cache :el-moved))
            "re-claimed under a new parent, still mounted, never retired")
        (is (nil? (cache/get-slot-cache :el-old-parent))
            "the parent that actually left is retired")))))

(deftest fragment-call-site-retires-with-its-fragment-and-not-before
  (testing "the keyed-cache leak (dead fragment) and the PR#39 bug (live
            fragment evicted via a dead parent) — both structural now"
    (with-ctx [_ctx]
      (let [{:keys [discharge]} (disch/make-mock-discharge)
            fragment (assoc (frag/keyed-fragment [(li "a")] nil) :addr :el-frag)
            with-frag (vn :div :el-root (vn :section :el-sec fragment))
            ;; the fragment SURVIVES a parent churn (moves to a new section)
            churned (vn :div :el-root (vn :article :el-sec2 fragment))
            without (vn :div :el-root nil)]
        (cache/set-keyed-cache! :el-frag {:by-key {} :items-by-key {}
                                          :order ["a"] :was-sync? true})
        (commit/retire-dead! discharge with-frag churned)
        (is (some? (cache/get-keyed-cache :el-frag))
            "live fragment survives its dead parent (PR#39, structurally)")
        (commit/retire-dead! discharge churned without)
        (is (nil? (cache/get-keyed-cache :el-frag))
            "dead fragment's keyed cache retired — no cascade required")))))
