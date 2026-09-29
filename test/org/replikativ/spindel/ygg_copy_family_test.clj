(ns org.replikativ.spindel.ygg-copy-family-test
  "Copy families: k alternatives of one world that settle at most once, and
  the structural grades that decide whether a world may be copied.

  Systems are in-memory G-Sets. A toy book stands in for an accounting system:
  worlds hold drafts under provisional ids; a gapless legal number is issued
  only when a merge reaches the root world (`:realize`)."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [clojure.set :as set]
            [yggdrasil.protocols :as yp]
            [yggdrasil.convergent.gset :as g]))

(defn- mem-gset [id]
  (g/gset id {:store-config {:backend :memory :id (random-uuid)}} {:sync? true}))

(defn- add! [fh sys-id x]
  (ygg/with-fork fh
    (swap! (ygg/system-signal sys-id) (fn [s] (g/conj s x)))))

(defn- elements
  ([sys-id] (g/elements (ygg/system sys-id)))
  ([ctx sys-id] (binding [ec/*execution-context* ctx] (elements sys-id))))

(defn- thrown-type [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(deftest one-member-of-a-family-merges
  (let [ctx (sp/create-execution-context)]
    (sp/with-context ctx
      (ygg/register! (mem-gset "kb"))
      (let [w (ygg/fork!)
            _ (add! w "kb" :before-copy)
            copies (ygg/copy-fork! w 3)]
        (doseq [[i c] (map-indexed vector copies)] (add! c "kb" (keyword (str "c" i))))
        (testing "the copied handle is consumed"
          (is (= ::ygg/stale-fork-handle (thrown-type #(ygg/merge-fork! w)))))
        (testing "concurrent merges: exactly one wins"
          (let [outcomes (mapv deref (mapv (fn [c] (future (try (ygg/merge-fork! c) :merged
                                                                (catch clojure.lang.ExceptionInfo e
                                                                  (:type (ex-data e))))))
                                           copies))
                winner (first (keep-indexed (fn [i o] (when (= :merged o) i)) outcomes))]
            (is (= 1 (count (filter #{:merged} outcomes))))
            (is (= 2 (count (filter #{::ygg/copy-family-settled} outcomes))))
            (is (= #{:before-copy (keyword (str "c" winner))} (elements "kb"))
                "the parent has the copied world and the winner's write, nothing else")
            (doseq [[i c] (map-indexed vector copies) :when (not= i winner)]
              (ygg/discard-fork! c))
            (is (= :merged (:status (ygg/copy-family (first copies)))))))))))

(deftest copies-of-a-copy-join-the-family
  (let [ctx (sp/create-execution-context)]
    (sp/with-context ctx
      (ygg/register! (mem-gset "kb"))
      (let [w (ygg/fork!)
            [a b] (ygg/copy-fork! w 2)
            _ (add! a "kb" :a)
            [a1 a2] (ygg/copy-fork! a 2)]
        (is (= (:id (ygg/copy-family b)) (:id (ygg/copy-family a1))))
        (add! a2 "kb" :a2)
        (ygg/merge-fork! a2)
        (is (= #{:a :a2} (elements "kb")) "a2 merged into a, a into w, w into the parent")
        (is (= ::ygg/copy-family-settled (thrown-type #(ygg/merge-fork! b))))
        (is (= ::ygg/copy-family-settled (thrown-type #(ygg/merge-fork! a1))))
        (ygg/discard-fork! a1)
        (ygg/discard-fork! b)
        (is (= #{:a :a2} (elements "kb")))))))

(deftest discarding-every-copy-discards-the-world
  (let [ctx (sp/create-execution-context)]
    (sp/with-context ctx
      (ygg/register! (mem-gset "kb"))
      (let [w (ygg/fork!)
            _ (add! w "kb" :w)
            copies (ygg/copy-fork! w 2)]
        (run! ygg/discard-fork! copies)
        (is (= #{} (elements "kb")))
        (is (= :discarded (:status (ygg/copy-family (first copies)))))
        (is (= :discarded (get-in (ygg/copy-family (first copies))
                                  [:members (:fork-id w) :settled])))))))

(deftest merging-an-unmodified-copy-is-the-identity
  (let [ctx (sp/create-execution-context)]
    (sp/with-context ctx
      (ygg/register! (-> (mem-gset "kb") (g/conj :base)))
      (let [[c] (ygg/copy-fork! (ygg/fork!) 1)]
        (ygg/merge-fork! c)
        (is (= #{:base} (elements "kb")))))))

(deftest copying-is-refused-for-state-that-may-not-be-copied
  (doseq [[opts expected] [[{:grade :affine} :affine]
                           [{:grade :linear} :linear]
                           [{:grade :divisible} :divisible]]]
    (let [ctx (sp/create-execution-context)]
      (sp/with-context ctx
        (ygg/register! (mem-gset "kb") opts)
        (let [w (ygg/fork!)]
          (is (= {"kb" expected}
                 (try (ygg/copy-fork! w 2) nil
                      (catch clojure.lang.ExceptionInfo e (:systems (ex-data e))))))
          (is (ygg/open-fork? w) "a refused copy leaves the handle open")))))
  (testing "a system shared with the parent is linear"
    (let [ctx (sp/create-execution-context)]
      (sp/with-context ctx
        (ygg/register! (reify yp/SystemIdentity
                         (system-id [_] "plain")
                         (system-type [_] :plain)
                         (capabilities [_] {})))
        (is (= ::ygg/copy-forbidden (thrown-type #(ygg/copy-fork! (ygg/fork!) 2))))))))

(deftest discarding-a-relevant-system-compensates
  (let [ctx (sp/create-execution-context)
        compensations (atom [])]
    (sp/with-context ctx
      (ygg/register! (mem-gset "ledger")
                     {:grade :relevant
                      :compensate (fn [{:keys [system-id child-ctx parent-ctx]}]
                                    (swap! compensations conj
                                           [system-id (set/difference
                                                       (elements child-ctx system-id)
                                                       (elements parent-ctx system-id))]))})
      (let [w (ygg/fork!)
            _ (add! w "ledger" :posting)
            [c1 c2] (ygg/copy-fork! w 2)]
        (add! c1 "ledger" :c1-posting)
        (ygg/discard-fork! c1)
        (ygg/discard-fork! c2)
        (is (= [["ledger" #{:c1-posting}]
                ["ledger" #{}]
                ["ledger" #{:posting}]]
               @compensations)
            "each discarded world compensates what it added to the world it came from:
             the copies, then the copied world")))))

(deftest a-toy-book-numbers-only-what-settles
  ;; Worlds draft invoices under provisional ids; the legal journal lives
  ;; outside every world and is gapless. Only a merge into the root realizes.
  (let [ctx (sp/create-execution-context)
        journal (atom {:next 1 :numbers {}})
        realized (atom 0)
        realize (fn [{:keys [system-id parent-ctx]}]
                  (swap! realized inc)
                  (swap! journal
                         (fn [j]
                           (reduce (fn [j draft]
                                     (if (contains? (:numbers j) draft)
                                       j
                                       (-> j (assoc-in [:numbers draft] (:next j)) (update :next inc))))
                                   j (sort-by str (elements parent-ctx system-id))))))]
    (sp/with-context ctx
      (ygg/register! (mem-gset "book") {:grade :linear :realize realize})
      (dotimes [round 2]
        (let [copies (ygg/copy-fork! (ygg/fork!) 3)
              drafts (mapv (fn [i] (keyword (str "draft-" round "-" i))) (range 3))]
          (doseq [[c d] (map vector copies drafts)] (add! c "book" d))
          (ygg/merge-fork! (second copies))
          (ygg/discard-fork! (first copies))
          (ygg/discard-fork! (nth copies 2))))
      (is (= {:draft-0-1 1 :draft-1-1 2} (:numbers @journal))
          "discarded copies drafted too, and consumed no number")
      (is (= 2 @realized) "the intermediate merge into the copied world realizes nothing"))))

(deftest a-refused-admission-leaves-the-world-as-it-was
  (let [ctx (sp/create-execution-context)]
    (sp/with-context ctx
      (ygg/register! (mem-gset "kb"))
      (let [w (ygg/fork!)
            _ (add! w "kb" :mine)
            seen (atom nil)]
        (is (= ::refused
               (thrown-type #(ygg/copy-fork! w 3 {:admit (fn [copies]
                                                           (reset! seen copies)
                                                           (throw (ex-info "no" {:type ::refused})))}))))
        (is (= 3 (count @seen)) "admission sees every copy")
        (is (every? #(= :discarded (:status (ygg/fork-disposition %))) @seen) "the copies are gone")
        (is (ygg/open-fork? w) "the world is still its owner's, not a family's")
        (is (nil? (:family w)))
        (ygg/merge-fork! w)
        (is (= #{:mine} (elements "kb")))))))
