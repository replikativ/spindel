(ns org.replikativ.spindel.dom.node-identity-test
  "DOM node IDENTITY and ORDER — the two things a vdom must never get wrong.

   The existing MockDischarge is structurally blind to both: it does not model
   `childNodes`, so a delta that inserts at the wrong index looks identical to
   one that inserts at the right index. Both bugs below lived behind that
   blindness. So this namespace brings its own discharge that keeps a real
   children vector."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.dom.cache :as cache]
            [org.replikativ.spindel.dom.fragment :as frag]))

;; ---------------------------------------------------------------------------
;; Slot → child index
;;
;; A SLOT is a position in the source (one child expression). A CHILD is a DOM
;; node. They are NOT the same: a nil slot flattens to zero nodes, an ifor-each
;; slot flattens to many. Every delta path that reaches the DOM must be a CHILD
;; index — and the conversion is `slot-base-index`.
;; ---------------------------------------------------------------------------

(defn- slots-of
  "Build a slot vector: :nil, :single, or :keyed with n items."
  [& specs]
  (mapv (fn [spec]
          (cond
            (= :nil spec)     {:type :nil :value nil}
            (number? spec)    {:type :keyed
                               :value (frag/->KeyedFragment (vec (repeat spec :item)) [])}
            :else             {:type :single :value spec}))
        specs))

(deftest fragment-deltas-carry-a-child-index-not-a-slot-index
  (testing "an ifor-each APPEARING after other children must insert AFTER them.

            :add-fragment used to fall through adjust-delta-paths unadjusted, so
            discharge received a SLOT index and used it as a CHILD index. With a
            preceding nil slot (zero nodes) or a preceding fragment (many), those
            differ — and the list silently materialised in the wrong place."
    ;; [single, single, <the fragment>] → the fragment's children start at 2
    (let [slots  (slots-of :a :b 3)
          deltas [{:delta :add-fragment :path [2]
                   :value (frag/->KeyedFragment [:x :y :z] [])}]
          [adj]  (cache/adjust-delta-paths slots deltas)]
      (is (= [2] (:path adj))
          "two single slots precede it ⇒ child index 2"))

    ;; a preceding NIL slot occupies a slot but NO child: slot 2 → child 1
    (let [slots  (slots-of :a :nil 3)
          deltas [{:delta :add-fragment :path [2]
                   :value (frag/->KeyedFragment [:x :y :z] [])}]
          [adj]  (cache/adjust-delta-paths slots deltas)]
      (is (= [1] (:path adj))
          "a nil slot flattens to ZERO children — slot 2 is child 1"))

    ;; a preceding FRAGMENT occupies one slot but MANY children: slot 2 → child 4
    (let [slots  (slots-of :a 3 2)
          deltas [{:delta :add-fragment :path [2]
                   :value (frag/->KeyedFragment [:x :y] [])}]
          [adj]  (cache/adjust-delta-paths slots deltas)]
      (is (= [4] (:path adj))
          "1 single + a 3-item fragment precede it — slot 2 is child 4"))))

(deftest fragment-removal-and-replacement-too
  (testing "the same conversion is needed on the way out and on replacement —
            they were all in the same unadjusted default branch"
    (let [slots (slots-of :a :nil 2)]
      (doseq [kind [:remove-fragment :replace-with-fragment
                    :replace-fragment-with-single]]
        (let [[adj] (cache/adjust-delta-paths
                     slots [{:delta kind :path [2] :value :v :old-value :o}])]
          (is (= [1] (:path adj))
              (str kind " must carry a child index, not a slot index")))))))

(deftest simple-deltas-unchanged
  (testing "the conversion that already worked still works"
    (let [slots  (slots-of :a :nil 3)
          [adj]  (cache/adjust-delta-paths
                  slots [{:delta :update :path [2] :value :v}])]
      (is (= [1] (:path adj))))))

;; ---------------------------------------------------------------------------
;; move-child! — see browser.cljs. A DOM move must MOVE the node, not destroy
;; and recreate it: `removeChild` + `insertBefore` runs the removing steps, which
;; discard an <iframe>'s browsing context, a <video>'s srcObject, a WebGL
;; context. `Element.moveBefore()` preserves them. Verified in Chromium; the JVM
;; test below pins only the INDEX arithmetic, which is the part that can be
;; got wrong silently (moveBefore is atomic, so the child is still present when
;; the reference node is chosen — indices do NOT shift as they did before).
;; ---------------------------------------------------------------------------

(defn- move-ref-index
  "Which sibling does the node land BEFORE, given the atomic-move semantics?
   Mirrors browser.cljs/move-child!."
  [n from to]
  (when (not= from to)
    (if (< from to) (inc to) to)))

(defn- simulate-move
  "Apply the move to a vector, using the ref computed above, and report where
   the moved element ended up. The invariant: it lands at `to`."
  [xs from to]
  (let [child (nth xs from)
        ref-i (move-ref-index (count xs) from to)
        ref   (when (and ref-i (< ref-i (count xs))) (nth xs ref-i))
        without (vec (concat (subvec xs 0 from) (subvec xs (inc from))))
        pos     (if ref
                  (.indexOf ^java.util.List without ref)
                  (count without))]
    (vec (concat (subvec without 0 pos) [child] (subvec without pos)))))

(deftest atomic-move-lands-at-the-requested-index
  (testing "for EVERY (from,to) the moved child must end up at `to`.

            The old code removed the child first and indexed the shortened list.
            moveBefore is atomic — the child is still there — so the reference
            node must be chosen with the shift accounted for. Getting it wrong is
            an off-by-one that silently misorders lists."
    (let [xs [:a :b :c :d :e]]
      (doseq [from (range 5)
              to   (range 5)
              :when (not= from to)]
        (let [moved (nth xs from)
              out   (simulate-move xs from to)]
          (is (= to (.indexOf ^java.util.List out moved))
              (str "move " from " → " to " landed wrong: " out)))))))
