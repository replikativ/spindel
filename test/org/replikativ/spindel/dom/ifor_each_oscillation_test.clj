(ns org.replikativ.spindel.dom.ifor-each-oscillation-test
  "Regression test for `ifor-each` against an *oscillating source* — a
  key that is added, then removed, then added again across successive
  renders.

  Why this matters: `ifor-each` is delta-driven. Its producer
  (`build-seq-diff`) is authoritative on `:new` and emits a typed
  `:seq-diff` (grow / shrink / permutation / change). The discharge
  layer (`apply-seq-diff!`) realises that diff onto real DOM children.
  If a source briefly drops a key and brings it back — e.g. an
  optimistic-overlay db value that flickers, a network reorder, a
  re-query race — the foreach must emit a clean shrink followed by a
  clean grow, and the discharge must remove exactly the dropped node
  and insert exactly one fresh node. A mismatch leaves a *duplicated*
  DOM child (the classic symptom: the same block rendered twice).

  This guards the spindel side of that contract end-to-end:
  `for-each*` → KeyedFragment `:seq-diff` → `apply-seq-diff!`."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.dom.elements :as el]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.dom.render :as render]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

(defn clean-context-fixture [f]
  (binding [ec/*execution-context* nil]
    (f)))

(use-fixtures :each clean-context-fixture)

(defn- net-children
  "Net child count of `parent-id` from a MockDischarge op log:
  append/insert add a child, remove drops one, replace is neutral."
  [log parent-id]
  (reduce (fn [n {:keys [op parent]}]
            (if (= parent parent-id)
              (case op
                (:append-child :insert-child) (inc n)
                :remove-child (dec n)
                n)
              n))
          0
          log))

(defn- count-ops [log parent-id op-kw]
  (count (filter #(and (= op-kw (:op %)) (= parent-id (:parent %))) log)))

(deftest test-ifor-each-add-remove-add-no-duplication
  (testing "A key added, removed, then re-added across renders must leave
            exactly one DOM node for it — never a duplicate."
    (with-ctx [ctx]
      (let [source     (sig/signal [{:id "a"} {:id "b"} {:id "c"}])
            ;; Plain-vnode render-fn → for-each* sync path, mirroring the
            ;; real wiki block list (render-block returns a plain vnode).
            render-fn  (fn [item] (el/li {:key (:id item)} (:id item)))
            parent-spin (spin
                         (let [{:keys [new]} (track source)]
                           (el/ul {:class "items"}
                                  (foreach/for-each*
                                   {:file "test" :line 1 :column 1}
                                   :id render-fn new))))
            {:keys [discharge log]} (disch/make-mock-discharge)]
        (render/render-spin! nil parent-spin discharge)
        @parent-spin
        (await-drain ctx)

        (let [ul-id (->> @log
                         (filter #(and (= :create-element (:op %))
                                       (= :ul (:tag %))))
                         first :id)]
          (is (some? ul-id) "a <ul> element was created")
          (is (= 3 (net-children @log ul-id)) "initial mount: 3 children")

          ;; (1) add d
          (reset! source [{:id "a"} {:id "b"} {:id "c"} {:id "d"}])
          (await-drain ctx)
          (is (= 4 (net-children @log ul-id)) "after add d: 4 children")

          ;; (2) remove d — the source momentarily drops the key
          (reset! source [{:id "a"} {:id "b"} {:id "c"}])
          (await-drain ctx)
          (is (= 3 (net-children @log ul-id)) "after remove d: 3 children")

          ;; (3) re-add d — the key comes back
          (reset! source [{:id "a"} {:id "b"} {:id "c"} {:id "d"}])
          (await-drain ctx)
          (is (= 4 (net-children @log ul-id))
              (str "after re-add d the <ul> must have exactly 4 children — "
                   "a duplicated node would push this to 5. Got "
                   (net-children @log ul-id)))

          ;; Exactly one <ul> across the whole sequence — the parent spin
          ;; re-completes but must reuse its element.
          (is (= 1 (->> @log
                        (filter #(and (= :create-element (:op %))
                                      (= :ul (:tag %))))
                        count))
              "exactly one <ul> created across all renders")

          ;; Op-level shape: the oscillation is one remove (step 2) and
          ;; two post-mount inserts (steps 1 and 3). A duplication bug
          ;; shows up as an extra insert with no matching remove.
          (is (= 1 (count-ops @log ul-id :remove-child))
              "exactly one remove emitted (the dropped d)")
          (is (= 2 (count-ops @log ul-id :insert-child))
              "exactly two post-mount inserts emitted (add d, re-add d)"))))))

(deftest test-ifor-each-repeated-oscillation-stays-bounded
  (testing "Many add/remove cycles of the same key never accumulate
            stale DOM children."
    (with-ctx [ctx]
      (let [base       [{:id "a"} {:id "b"}]
            with-x     (conj base {:id "x"})
            source     (sig/signal base)
            render-fn  (fn [item] (el/li {:key (:id item)} (:id item)))
            parent-spin (spin
                         (let [{:keys [new]} (track source)]
                           (el/ul {}
                                  (foreach/for-each*
                                   {:file "test" :line 2 :column 1}
                                   :id render-fn new))))
            {:keys [discharge log]} (disch/make-mock-discharge)]
        (render/render-spin! nil parent-spin discharge)
        @parent-spin
        (await-drain ctx)
        (let [ul-id (->> @log
                         (filter #(and (= :create-element (:op %))
                                       (= :ul (:tag %))))
                         first :id)]
          (dotimes [_ 6]
            (reset! source with-x)
            (await-drain ctx)
            (is (= 3 (net-children @log ul-id)) "with x: 3 children")
            (reset! source base)
            (await-drain ctx)
            (is (= 2 (net-children @log ul-id)) "without x: 2 children"))
          ;; Land on the with-x state and confirm a clean final count.
          (reset! source with-x)
          (await-drain ctx)
          (is (= 3 (net-children @log ul-id))
              "after 6 oscillation cycles the list is still exactly 3 long"))))))
