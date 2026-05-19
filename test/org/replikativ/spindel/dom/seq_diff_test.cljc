(ns org.replikativ.spindel.dom.seq-diff-test
  "Tests for the SequenceAlgebra-native discharge entry point
   `apply-seq-diff!`. Verifies that the DOM operations emitted by the
   discharge layer leave the parent's child list in exactly the order
   that `SequenceAlgebra/-apply-deltas` would compute on the
   corresponding token vector.

   Token model: each child position is identified by a token. Prev
   tokens are `[:prev i]` (initial mount index i); positions named by
   `:change` carry a `[:new k]` token. After the diff is applied,
   reconstructing the final child list from the discharge log must
   match the algebra's `apply-deltas` on the equivalent token vector."
  (:require #?(:clj  [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer-macros [deftest is testing use-fixtures]])
            [org.replikativ.spindel.dom.core :as dom]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.incremental.algebra :as a]
            [org.replikativ.spindel.incremental.sequence-algebra :as sa]))

;; Tests that exercise shrink / replace paths trigger
;; `call-refs-on-unmount!` which evicts the dom-cache and needs an
;; execution context bound. Provide one for every test in this ns.
(use-fixtures :each
  (fn [t]
    (let [c (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* c]
          (t))
        (finally
          (ctx/stop-context! c))))))

;; =============================================================================
;; Test infrastructure
;; =============================================================================

(defn mk-vnode
  "Build a vnode whose :addr is namespaced by `token` so each test child
   has a unique stable address. The vnode is plain (no refs); we don't
   exercise lifecycle here — see seq-diff-ref-test for that."
  [token]
  (-> (dom/make-vnode :div {:class (str "child-" (pr-str token))})
      (assoc :addr [::test token])))

(defn render-initial-children!
  "Render a parent with `tokens` as children. Returns a vector of
   element IDs (in order) and the vector of vnodes."
  [discharge tokens]
  (let [parent-vnode (dom/make-vnode :div {} (mapv mk-vnode tokens))
        _parent-el (disch/render-initial! discharge parent-vnode)
        vnodes (:children parent-vnode)
        eids (mapv #(disch/get-element discharge (:addr %)) vnodes)]
    {:parent-vnode parent-vnode
     :parent-el _parent-el
     :vnodes (vec vnodes)
     :eids eids}))

(defn replay-child-ops
  "Replay the discharge log onto an initial vector of child tokens,
   returning the final vector. Only ops on `parent-el` are considered.

   The simulator knows how to handle:
     :insert-child  insert child at index
     :remove-child  remove at index
     :replace-child replace at index
     :move-child    move from→to (relative to *current* layout)
     :append-child  append (for initial mount only)"
  [parent-el initial-children ops]
  (reduce
   (fn [v op]
     (case (:op op)
       :insert-child
       (if (= parent-el (:parent op))
         (let [{:keys [child index]} op]
           (vec (concat (subvec v 0 index) [child] (subvec v index))))
         v)

       :remove-child
       (if (= parent-el (:parent op))
         (let [{:keys [index]} op]
           (vec (concat (subvec v 0 index) (subvec v (inc index)))))
         v)

       :replace-child
       (if (= parent-el (:parent op))
         (let [{:keys [child index]} op]
           (assoc v index child))
         v)

       :move-child
       (if (= parent-el (:parent op))
         (let [{:keys [from to]} op
               item (nth v from)
               without (vec (concat (subvec v 0 from) (subvec v (inc from))))]
           (vec (concat (subvec without 0 to) [item] (subvec without to))))
         v)

       :append-child
       (if (= parent-el (:parent op))
         (conj v (:child op))
         v)

       v))
   initial-children
   ops))

(defn fresh-tokens-for-change
  "For a :change map, return a map {k token} of unique fresh tokens
   for each entry. Tokens are unique gensyms so we can distinguish
   replaced positions from surviving ones."
  [change]
  (into {} (map (fn [[k _]] [k (gensym "new-")]) change)))

(defn expected-tokens-via-algebra
  "Apply the SequenceAlgebra diff to a vector of prev tokens, using
   `fresh-tokens` to override `:change` entries. Returns the resulting
   token vector — what the DOM should look like after `apply-seq-diff!`."
  [prev-tokens diff fresh-tokens]
  (let [degree (:degree diff)
        grow (:grow diff 0)
        ;; Build the diff with token-valued :change for the simulation.
        token-change (into {} (map (fn [[k _]] [k (get fresh-tokens k)])
                                   (:change diff {})))
        algebra-diff {:degree degree
                      :grow grow
                      :shrink (:shrink diff 0)
                      :permutation (:permutation diff {})
                      :change token-change
                      :freeze (:freeze diff #{})}
        ;; Algebra needs a vector of size (degree - grow).
        pre-vec (vec prev-tokens)]
    (a/apply-deltas sa/sequence-algebra pre-vec algebra-diff)))

(defn make-change-vnodes
  "Given a :change map keyed by post-shrink position and a
   `fresh-tokens` map matching it, build a {pos vnode} map where each
   vnode carries the corresponding fresh token in its :addr."
  [change fresh-tokens]
  (into {} (map (fn [[k _]]
                  [k (mk-vnode (get fresh-tokens k))])
                change)))

(defn check-diff!
  "Run a single round-trip: render `prev-tokens`, apply `diff`, then
   verify the resulting DOM token sequence equals what
   `SequenceAlgebra` predicts."
  [prev-tokens diff]
  (let [{:keys [discharge log]} (disch/make-mock-discharge)
        {:keys [parent-el vnodes eids]}
        (render-initial-children! discharge prev-tokens)
        ;; Snapshot initial children.
        initial-children eids
        ;; Build fresh tokens and corresponding new vnodes for :change.
        fresh (fresh-tokens-for-change (:change diff))
        change-vnodes (make-change-vnodes (:change diff) fresh)
        diff-with-vnodes (assoc diff :change change-vnodes)
        ;; Drop the initial render ops from the log so we only consider
        ;; what apply-seq-diff! emits.
        log-before (count @log)]
    (disch/apply-seq-diff! discharge parent-el diff-with-vnodes vnodes)
    (let [seq-diff-ops (subvec @log log-before)
          ;; Replay the seq-diff ops on top of the initial children.
          final-children (replay-child-ops parent-el initial-children seq-diff-ops)
          ;; Map back: each child eid is either an old eid (with prev
          ;; token) or a freshly-created one (with new token).
          eid->token (merge
                      (into {} (map vector eids prev-tokens))
                      ;; For fresh elements, look up via discharge's
                      ;; address registry using the new vnode addrs.
                      (into {} (for [[k vnode] change-vnodes
                                     :let [eid (disch/get-element
                                                discharge (:addr vnode))]
                                     :when eid]
                                 [eid (get fresh k)])))
          final-tokens (mapv eid->token final-children)
          expected (expected-tokens-via-algebra prev-tokens diff fresh)]
      {:expected expected
       :actual final-tokens
       :match? (= expected final-tokens)
       :ops seq-diff-ops})))

;; =============================================================================
;; Focused tests — one per operation kind
;; =============================================================================

(deftest test-empty-diff
  (testing "Empty diff over non-empty list is a no-op"
    (let [{:keys [match? expected actual ops]}
          (check-diff! [:a :b :c]
                       {:degree 3 :grow 0 :shrink 0
                        :permutation {} :change {}})]
      (is match? (str "expected " expected ", got " actual))
      (is (empty? ops) "No DOM ops should be emitted"))))

(deftest test-pure-grow-at-tail
  (testing "Pure grow at tail appends new children"
    (let [{:keys [match? expected actual]}
          (check-diff! [:a :b]
                       {:degree 4 :grow 2 :shrink 0
                        :permutation {}
                        :change {2 :placeholder-x 3 :placeholder-y}})]
      (is match? (str "expected " expected ", got " actual)))))

(deftest test-pure-shrink-at-tail
  (testing "Pure shrink at tail removes trailing children"
    (let [{:keys [match? expected actual]}
          (check-diff! [:a :b :c :d]
                       {:degree 4 :grow 0 :shrink 2
                        :permutation {} :change {}})]
      (is match? (str "expected " expected ", got " actual)))))

(deftest test-pure-permutation-swap
  (testing "Pure swap of two adjacent children"
    (let [{:keys [match? expected actual]}
          (check-diff! [:a :b :c]
                       {:degree 3 :grow 0 :shrink 0
                        :permutation {0 1, 1 0}
                        :change {}})]
      (is match? (str "expected " expected ", got " actual)))))

(deftest test-permutation-reverse
  (testing "Reverse all children"
    (let [{:keys [match? expected actual]}
          (check-diff! [:a :b :c :d]
                       {:degree 4 :grow 0 :shrink 0
                        :permutation {0 3, 1 2, 2 1, 3 0}
                        :change {}})]
      (is match? (str "expected " expected ", got " actual)))))

(deftest test-change-at-position
  (testing "Change at single position replaces that DOM element"
    (let [{:keys [match? expected actual]}
          (check-diff! [:a :b :c]
                       {:degree 3 :grow 0 :shrink 0
                        :permutation {} :change {1 :placeholder}})]
      (is match? (str "expected " expected ", got " actual)))))

(deftest test-insert-in-middle
  (testing "Insert one child in the middle (grow + permutation + change)"
    ;; Insert :x at position 1 in [:a :b :c]:
    ;; → final = [:a :x :b :c]
    ;; degree = 4, grow = 1, shrink = 0
    ;; π: new slot 3 → 1, prev 1 → 2, prev 2 → 3
    (let [{:keys [match? expected actual]}
          (check-diff! [:a :b :c]
                       {:degree 4 :grow 1 :shrink 0
                        :permutation {3 1, 1 2, 2 3}
                        :change {1 :placeholder-x}})]
      (is match? (str "expected " expected ", got " actual)))))

(deftest test-remove-in-middle
  (testing "Remove one child from the middle (permutation + shrink)"
    ;; Remove :b from [:a :b :c]:
    ;; → final = [:a :c]
    ;; degree = 3, grow = 0, shrink = 1
    ;; π: prev 1 → 2 (doomed; goes to tail), prev 2 → 1
    (let [{:keys [match? expected actual]}
          (check-diff! [:a :b :c]
                       {:degree 3 :grow 0 :shrink 1
                        :permutation {1 2, 2 1}
                        :change {}})]
      (is match? (str "expected " expected ", got " actual)))))

(deftest test-combined-grow-permute-shrink-change
  (testing "All four operations in a single diff"
    ;; Start: [:a :b :c]
    ;; Want:  [:c :a :y]
    ;; - Remove :b
    ;; - Move :c to front
    ;; - Replace position 2 with new :y
    ;; degree = 3 + grow(1) = 4 wait — let's think:
    ;; size-before = 3, size-after = 3, so grow = shrink.
    ;; Simplest: grow=1, shrink=1, π must produce the swap.
    ;; new positions: [:c :a :y]
    ;;   pos 0 ← prev 2 (:c)
    ;;   pos 1 ← prev 0 (:a)
    ;;   pos 2 ← grown slot 3, replaced by :y via :change
    ;;   doomed: prev 1 (:b) → position 3 (≥ size-after=3)
    ;; π: 2→0, 0→1, 1→3, 3→2  (i.e., grown slot 3 ends at new pos 2)
    (let [{:keys [match? expected actual]}
          (check-diff! [:a :b :c]
                       {:degree 4 :grow 1 :shrink 1
                        :permutation {2 0, 0 1, 1 3, 3 2}
                        :change {2 :placeholder-y}})]
      (is match? (str "expected " expected ", got " actual)))))

;; =============================================================================
;; Reconciliation invariants
;; =============================================================================

(deftest test-no-replace-when-no-change
  (testing "Permutation-only diff should not emit any :replace-child"
    (let [{:keys [discharge log]} (disch/make-mock-discharge)
          {:keys [parent-el vnodes]}
          (render-initial-children! discharge [:a :b :c :d])
          log-before (count @log)]
      (disch/apply-seq-diff! discharge parent-el
                             {:degree 4 :grow 0 :shrink 0
                              :permutation {0 3, 1 2, 2 1, 3 0}
                              :change {}}
                             vnodes)
      (let [ops (subvec @log log-before)
            replace-ops (filter #(= :replace-child (:op %)) ops)
            create-ops (filter #(= :create-element (:op %)) ops)]
        (is (empty? replace-ops)
            "No :replace-child when there is no :change")
        (is (empty? create-ops)
            "No :create-element when there is no :change")))))

(deftest test-reconcile-in-place-for-compatible-change
  (testing "Change of a vnode that is reconcilable to the previous reuses the element"
    ;; Build prev with explicit addr, then change with same tag/key/addr.
    (let [{:keys [discharge log]} (disch/make-mock-discharge)
          old-vnode (-> (dom/make-vnode :div {:class "old"})
                        (assoc :key "k1" :addr ::stable-addr))
          parent-vnode (dom/make-vnode :div {} [old-vnode])
          parent-el (disch/render-initial! discharge parent-vnode)
          new-vnode (-> (dom/make-vnode :div {:class "new"})
                        (assoc :key "k1" :addr ::stable-addr))
          log-before (count @log)]
      (disch/apply-seq-diff! discharge parent-el
                             {:degree 1 :grow 0 :shrink 0
                              :permutation {} :change {0 new-vnode}}
                             [old-vnode])
      (let [ops (subvec @log log-before)
            replace-ops (filter #(= :replace-child (:op %)) ops)
            set-attr-ops (filter #(and (= :set-attr (:op %))
                                       (= :class (:attr %))) ops)]
        (is (empty? replace-ops)
            "Compatible change must reconcile in place, not replace")
        (is (some #(= "new" (:value %)) set-attr-ops)
            "Class attribute should be updated on the surviving element")))))

(deftest test-replace-for-incompatible-change
  (testing "Change to a vnode with different :addr destroys and recreates"
    (let [{:keys [discharge log]} (disch/make-mock-discharge)
          old-vnode (-> (dom/make-vnode :div {:class "old"})
                        (assoc :addr ::addr-a))
          parent-vnode (dom/make-vnode :div {} [old-vnode])
          parent-el (disch/render-initial! discharge parent-vnode)
          new-vnode (-> (dom/make-vnode :span {:class "new"})
                        (assoc :addr ::addr-b))
          log-before (count @log)]
      (disch/apply-seq-diff! discharge parent-el
                             {:degree 1 :grow 0 :shrink 0
                              :permutation {} :change {0 new-vnode}}
                             [old-vnode])
      (let [ops (subvec @log log-before)
            replace-ops (filter #(= :replace-child (:op %)) ops)]
        (is (= 1 (count replace-ops))
            "Incompatible change must replace the element")))))

(deftest test-doomed-prev-elements-removed-tail-to-head
  (testing "Doomed prev positions (π(i) ≥ size-after) are removed in reverse order"
    (let [{:keys [discharge log]} (disch/make-mock-discharge)
          {:keys [parent-el vnodes]}
          (render-initial-children! discharge [:a :b :c :d :e])
          log-before (count @log)]
      ;; Shrink last 2: doomed are positions 3, 4.
      (disch/apply-seq-diff! discharge parent-el
                             {:degree 5 :grow 0 :shrink 2
                              :permutation {} :change {}}
                             vnodes)
      (let [ops (subvec @log log-before)
            remove-ops (filter #(and (= :remove-child (:op %))
                                     (= parent-el (:parent %))) ops)
            indices (mapv :index remove-ops)]
        (is (= [4 3] indices)
            "Doomed elements must be removed tail-to-head")))))

;; =============================================================================
;; Property-style: random diffs over small lists
;; =============================================================================

(defn- gen-token-vec [n]
  (vec (map #(keyword (str "t" %)) (range n))))

(defn- random-perm
  "Build a random total permutation on [0, n) as a sparse map (fixed
   points elided)."
  [n]
  (let [src (vec (range n))
        shuffled (shuffle src)]
    (->> (map-indexed (fn [i j] [i j]) shuffled)
         (filter (fn [[i j]] (not= i j)))
         (into {}))))

(deftest test-random-shrinks
  (testing "Random shrinks of various sizes leave the right tokens"
    (doseq [n (range 1 8)
            s (range 0 (inc n))]
      (let [{:keys [match? expected actual]}
            (check-diff! (gen-token-vec n)
                         {:degree n :grow 0 :shrink s
                          :permutation {} :change {}})]
        (is match?
            (str "n=" n " shrink=" s " — expected " expected ", got " actual))))))

(deftest test-random-grows
  (testing "Random grows of various sizes leave the right tokens"
    (doseq [n (range 0 6)
            g (range 0 5)]
      (let [change (into {} (map (fn [k] [k (gensym "new-")])
                                 (range n (+ n g))))
            {:keys [match? expected actual]}
            (check-diff! (gen-token-vec n)
                         {:degree (+ n g) :grow g :shrink 0
                          :permutation {} :change change})]
        (is match?
            (str "n=" n " grow=" g " — expected " expected ", got " actual))))))

(deftest test-random-permutations
  (testing "Random permutations leave tokens in the right order"
    (doseq [_ (range 30)
            n [3 4 5 6 7]]
      (let [tokens (gen-token-vec n)
            π (random-perm n)
            {:keys [match? expected actual]}
            (check-diff! tokens
                         {:degree n :grow 0 :shrink 0
                          :permutation π :change {}})]
        (is match?
            (str "n=" n " π=" π " — expected " expected ", got " actual))))))

(deftest test-random-changes-only
  (testing "Random changes at arbitrary positions update the right slots"
    (doseq [_ (range 30)
            :let [n (+ 3 (rand-int 5))
                  positions (set (take (inc (rand-int n))
                                       (shuffle (range n))))
                  change (into {} (map (fn [k] [k (gensym "new-")]) positions))]]
      (let [tokens (gen-token-vec n)
            {:keys [match? expected actual]}
            (check-diff! tokens
                         {:degree n :grow 0 :shrink 0
                          :permutation {} :change change})]
        (is match?
            (str "n=" n " change@" (sort (keys change))
                 " — expected " expected ", got " actual))))))

;; =============================================================================
;; Fragment-offset regression
;;
;; When a KeyedFragment (produced by ifor-each) is rendered as a
;; sibling of other elements (a heading above, a footer below), the
;; producer's seq-diff carries positions 0..N relative to the
;; fragment's children, NOT to parent.childNodes. Earlier the
;; discharge applied those positions as absolute parent.childNodes
;; indices and mutated the wrong rows. The fix derives the
;; fragment's offset from the first prev-vnode's DOM element via
;; `child-index-of`, and adds it to every index op.
;;
;; The MockDischarge can't know about DOM positions, but it CAN be
;; wired to return a stubbed `child-index-of` for testing. The
;; wrapper here intercepts that one protocol method and answers
;; with the configured offset; everything else delegates.
;; =============================================================================

(defrecord OffsetMockDischarge [inner offset-val]
  disch/PDischarge
  (create-element! [_ vnode]    (disch/create-element! inner vnode))
  (create-text!    [_ t]        (disch/create-text! inner t))
  (set-attribute!  [_ el a v]   (disch/set-attribute! inner el a v))
  (remove-attribute! [_ el a]   (disch/remove-attribute! inner el a))
  (append-child!   [_ p c]      (disch/append-child! inner p c))
  (insert-child!   [_ p c i]    (disch/insert-child! inner p c i))
  (remove-child!   [_ p i]      (disch/remove-child! inner p i))
  (replace-child!  [_ p c i]    (disch/replace-child! inner p c i))
  (move-child!     [_ p f t]    (disch/move-child! inner p f t))
  (child-index-of  [_ _p _c]    offset-val)
  (set-text-content! [_ el t]   (disch/set-text-content! inner el t))
  (get-element     [_ addr]     (disch/get-element inner addr))
  (set-element!    [_ addr el]  (disch/set-element! inner addr el))
  (remove-children-range! [this p s n]
    (disch/default-remove-children-range! this p s n))
  (insert-children! [this p cs s]
    (disch/default-insert-children! this p cs s)))

(defn- make-offset-discharge [offset-val]
  (let [{:keys [discharge log elements]} (disch/make-mock-discharge)]
    {:discharge (->OffsetMockDischarge discharge offset-val)
     :log       log
     :elements  elements}))

(deftest test-offset-shifts-remove-index
  (testing "When child-index-of returns N, doomed removes target N+i, not i"
    (let [offset 1
          {:keys [discharge log]} (make-offset-discharge offset)
          {:keys [parent-el vnodes]} (render-initial-children! discharge [:a :b :c])
          log-before (count @log)]
      ;; Shrink last element only. The doomed index inside the diff
      ;; is 2 (last prev position). With offset=1, the actual DOM
      ;; index should be 3, not 2.
      (disch/apply-seq-diff! discharge parent-el
                             {:degree 3 :grow 0 :shrink 1
                              :permutation {} :change {}}
                             vnodes)
      (let [ops (subvec @log log-before)
            remove-ops (filter #(and (= :remove-child (:op %))
                                     (= parent-el (:parent %))) ops)]
        (is (= 1 (count remove-ops)) "Exactly one remove emitted")
        (is (= 3 (:index (first remove-ops)))
            (str "Remove index should be 2+offset=3; got "
                 (:index (first remove-ops))))))))

(deftest test-offset-shifts-insert-index
  (testing "When child-index-of returns N, grown inserts go to N+k, not k"
    (let [offset 2
          {:keys [discharge log]} (make-offset-discharge offset)
          {:keys [parent-el vnodes]} (render-initial-children! discharge [:a :b])
          log-before (count @log)]
      ;; Grow by 2 at tail. Inserts at k=2 and k=3 should hit
      ;; parent.childNodes[4] and [5] when offset=2.
      (disch/apply-seq-diff! discharge parent-el
                             {:degree 4 :grow 2 :shrink 0
                              :permutation {}
                              :change {2 (mk-vnode :tok-x)
                                       3 (mk-vnode :tok-y)}}
                             vnodes)
      (let [ops (subvec @log log-before)
            inserts (filter #(and (= :insert-child (:op %))
                                  (= parent-el (:parent %))) ops)
            indices (mapv :index inserts)]
        (is (= 2 (count inserts)) "Two inserts emitted")
        (is (= [4 5] indices)
            (str "Insert indices should be [2+offset 3+offset] = [4 5]; got "
                 indices))))))

(deftest test-offset-shifts-move-and-replace
  (testing "Permutation+change with offset N: move/replace use N+pos"
    (let [offset 4
          {:keys [discharge log]} (make-offset-discharge offset)
          {:keys [parent-el vnodes]} (render-initial-children! discharge [:a :b :c])
          log-before (count @log)]
      ;; Swap 0↔2, change at new-pos 0. With offset=4:
      ;; move-child should be from (offset + 2) to (offset + 0) = from 6 to 4.
      (disch/apply-seq-diff! discharge parent-el
                             {:degree 3 :grow 0 :shrink 0
                              :permutation {0 2, 2 0}
                              :change {0 (mk-vnode :replaced-a)}}
                             vnodes)
      (let [ops (subvec @log log-before)
            moves (filter #(= :move-child (:op %)) ops)]
        ;; Multiple moves may be emitted to realise the swap; verify
        ;; ALL emitted move indices are within the offset range.
        (is (seq moves) "At least one move emitted for swap")
        (is (every? (fn [{:keys [from to]}]
                      (and (>= from offset) (>= to offset)))
                    moves)
            (str "All move indices should be ≥ offset=" offset
                 "; got " (mapv #(select-keys % [:from :to]) moves)))))))

(deftest test-offset-zero-matches-prior-behaviour
  (testing "Default offset (0) preserves the no-siblings behaviour the older tests verified"
    (let [{:keys [discharge log]} (make-offset-discharge 0)
          {:keys [parent-el vnodes]} (render-initial-children! discharge [:a :b :c])
          log-before (count @log)]
      (disch/apply-seq-diff! discharge parent-el
                             {:degree 3 :grow 0 :shrink 1
                              :permutation {} :change {}}
                             vnodes)
      (let [remove-op (first (filter #(= :remove-child (:op %))
                                     (subvec @log log-before)))]
        (is (= 2 (:index remove-op))
            "With offset=0, remove targets the bare diff index")))))
