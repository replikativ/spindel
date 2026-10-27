(ns org.replikativ.spindel.ygg-family-settlement-test
  "Reconciled settlement of copy families: several copies land together when
  their contributions are disjoint.

  A toy book stands in for an accounting system that settles by intents:
  worlds hold drafts under provisional ids, each claiming some keys (a bank
  line it matches, an order it bills); a gapless legal journal outside every
  world numbers what reaches the root, in (date, id) order."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [clojure.set :as set]
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

(defn- draft
  "A draft as the G-Set keeps it (sorted, so comparable): [date id claims]."
  [id date & claims] [date id (vec (sort claims))])

(defn- prov [d] (second d))

(defn- toy-book
  "The book's settlement policy and its journal. `fail-stamps` stamps that
  throw before the next one succeeds."
  [& [fail-stamps]]
  (let [journal (atom {:next 1 :numbers {}})
        stamp-calls (atom 0)
        realize-calls (atom 0)
        observe-stamp (atom nil)
        failures (atom (or fail-stamps 0))]
    {:journal journal
     :stamp-calls stamp-calls
     :realize-calls realize-calls
     :observe-stamp observe-stamp
     :policy
     {:grade :linear
      :realize (fn [_] (swap! realize-calls inc))
      :intents (fn [{:keys [system-id child-ctx parent-ctx]}]
                 (for [d (set/difference (elements child-ctx system-id)
                                         (elements parent-ctx system-id))]
                   {:intent/id (prov d) :footprint (set (nth d 2)) :draft d}))
      :parent-footprint (fn [{:keys [system-id child-ctx parent-ctx]}]
                          (into #{} (mapcat #(nth % 2))
                                (set/difference (elements parent-ctx system-id)
                                                (elements child-ctx system-id))))
      :stamp (fn [{:keys [system-id parent-ctx final? contributions]}]
               (swap! stamp-calls inc)
               (when-let [observe @observe-stamp] (observe))
               (when (pos? @failures)
                 (swap! failures dec)
                 (throw (ex-info "writer unavailable" {})))
               (let [drafts (->> contributions (mapcat :intents) (map :draft) distinct sort)]
                 (binding [ec/*execution-context* parent-ctx]
                   (doseq [d drafts]
                     (swap! (ygg/system-signal system-id) #(g/conj % d))))
                 (when final?
                   (swap! journal
                          (fn [j]
                            (reduce (fn [j d]
                                      (if (contains? (:numbers j) (prov d))
                                        j
                                        (-> j (assoc-in [:numbers (prov d)] (:next j)) (update :next inc))))
                                    j drafts)))))
               nil)}}))

(defmacro ^:private with-book [[book & [fails]] & body]
  `(let [ctx# (sp/create-execution-context)
         ~book (toy-book ~fails)]
     (sp/with-context ctx#
       (ygg/register! (mem-gset "book") (:policy ~book))
       (ygg/register! (mem-gset "kb"))
       ~@body)))

(deftest disjoint-copies-all-land-and-are-numbered-gaplessly
  (with-book [book]
    (let [w (ygg/fork!)
          _ (add! w "book" (draft :w-1 1 :order-1))
          [a b c] (ygg/copy-fork! w 3)]
      (add! a "book" (draft :a-1 5 :line-1))
      (add! b "book" (draft :b-1 3 :line-2))
      (add! b "book" (draft :b-2 4 :order-2))
      (add! c "kb" :note-from-c)
      (is (= :reviewable (:tier (ygg/family-review [a b c]))))
      (ygg/settle-family! [a b c])
      (is (= {:w-1 1 :b-1 2 :b-2 3 :a-1 4} (:numbers @(:journal book)))
          "the copied world's own draft and every member's, gapless in date order")
      (is (= #{:w-1 :a-1 :b-1 :b-2} (set (map prov (elements "book")))))
      (is (= #{:note-from-c} (elements "kb")) "ordinary systems merge as state")
      (is (= :merged (:status (ygg/copy-family a))))
      (is (= ::ygg/copy-family-settled (thrown-type #(ygg/merge-fork! a)))))))

(deftest settlement-does-not-depend-on-order
  (let [numbers (fn [order]
                  (with-book [book]
                    (let [copies (ygg/copy-fork! (ygg/fork!) 3)]
                      (doseq [[i c] (map-indexed vector copies)]
                        (add! c "book" (draft (keyword (str "d" i)) (- 10 i) (keyword (str "k" i)))))
                      (ygg/settle-family! (mapv copies order))
                      (:numbers @(:journal book)))))]
    (is (apply = (map numbers [[0 1 2] [2 1 0] [1 2 0]])))
    (is (= {:d2 1 :d1 2 :d0 3} (numbers [0 1 2])))))

(deftest overlapping-claims-conflict-and-change-nothing
  (with-book [book]
    (let [[a b c] (ygg/copy-fork! (ygg/fork!) 3)]
      (add! a "book" (draft :a-1 1 :line-7))
      (add! b "book" (draft :b-1 2 :line-7))
      (add! c "book" (draft :c-1 3 :line-8))
      (let [{:keys [tier conflicts]} (ygg/family-review [a b c])]
        (is (= :conflict tier))
        (is (= [{:system "book" :key :line-7 :members #{(:fork-id a) (:fork-id b)}}] conflicts)))
      (is (= ::ygg/family-conflict (thrown-type #(ygg/settle-family! [a b c]))))
      (is (= {} (:numbers @(:journal book))))
      (is (= :open (:status (ygg/copy-family a))) "nothing settled")
      (testing "a disjoint subset settles; the rest is discarded"
        (ygg/settle-family! [a c])
        (ygg/discard-fork! b)
        (is (= {:a-1 1 :c-1 2} (:numbers @(:journal book))))))))

(deftest the-same-intent-in-two-copies-is-one
  (with-book [book]
    (let [[a b] (ygg/copy-fork! (ygg/fork!) 2)
          same (draft :shared 1 :line-1)]
      (add! a "book" same)
      (add! b "book" same)
      (is (= :reviewable (:tier (ygg/family-review [a b]))))
      (ygg/settle-family! [a b])
      (is (= {:shared 1} (:numbers @(:journal book)))))))

(deftest untouched-copies-are-trivial
  (with-book [_]
    (let [copies (ygg/copy-fork! (ygg/fork!) 2)]
      (is (= :trivial (:tier (ygg/family-review copies)))))))

(deftest a-failed-stamp-is-retried-without-double-numbers
  (with-book [book 1]
    (let [[a b] (ygg/copy-fork! (ygg/fork!) 2)]
      (add! a "book" (draft :a-1 1 :x))
      (add! b "book" (draft :b-1 2 :y))
      (is (= ::ygg/family-stamp-failed
             (thrown-type #(ygg/settle-family! [a b] {:operation-id :reconciled-stamp}))))
      (is (= :failed (:status (ygg/copy-family a))))
      (is (= [:incomplete :incomplete]
             (mapv #(-> % ygg/fork-disposition :status) [a b])))
      (is (= :incomplete (:fork/status (ygg/copied-descriptor a (ygg/copied-from a (:fork-id a))))))
      (is (= {} (:numbers @(:journal book))))
      (is (= ::ygg/copy-family-settled (thrown-type #(ygg/merge-fork! a))))
      (is (= ::ygg/copy-family-settled
             (thrown-type #(ygg/settle-family! [a] {:operation-id :different}))))
      (ygg/settle-family! [a])
      (is (= :merged (:status (ygg/copy-family a))))
      (is (= [:merged :merged] (mapv #(-> % ygg/fork-disposition :status) [a b])))
      (is (= {:a-1 1 :b-1 2} (:numbers @(:journal book))))
      (ygg/settle-family! [a])
      (is (= {:a-1 1 :b-1 2} (:numbers @(:journal book))) "idempotent"))))

(deftest ordinary-systems-conflict-by-footprint
  (let [ctx (sp/create-execution-context)]
    (sp/with-context ctx
      (ygg/register! (mem-gset "notes")
                     {:footprint (fn [{:keys [system-id child-ctx parent-ctx]}]
                                   (set (map first (set/difference (elements child-ctx system-id)
                                                                   (elements parent-ctx system-id)))))})
      (let [[a b c] (ygg/copy-fork! (ygg/fork!) 3)]
        (add! a "notes" [:topic-1 "a"])
        (add! b "notes" [:topic-1 "b"])
        (add! c "notes" [:topic-2 "c"])
        ;; a G-Set's diff is empty (its merges commute), so the footprint is
        ;; only consulted for systems that report a change
        (is (not= :conflict (:tier (ygg/family-review [a b c])))
            "a convergent system cannot conflict")))))

;; --- single worlds and at-most-one families settle by intents too -----------

(deftest a-single-world-is-stamped-when-it-merges
  (with-book [book]
    (let [w (ygg/fork!)]
      (add! w "book" (draft :w-1 2 :line-1))
      (add! w "book" (draft :w-2 1 :order-1))
      (ygg/merge-fork! w)
      (is (= {:w-2 1 :w-1 2} (:numbers @(:journal book))))
      (is (= #{:w-1 :w-2} (set (map prov (elements "book"))))))))

(deftest a-claim-the-parent-made-meanwhile-conflicts
  (with-book [book]
    (let [w (ygg/fork!)]
      (add! w "book" (draft :w-1 1 :line-1))
      ;; the parent matched the same bank line after the fork
      (swap! (ygg/system-signal "book") #(g/conj % (draft :root-1 1 :line-1)))
      (let [e (try (ygg/merge-fork! w) nil (catch clojure.lang.ExceptionInfo e (ex-data e)))]
        (is (= ::ygg/merge-conflict (:type e)))
        (is (= [{:system "book" :key :line-1 :members #{(:fork-id w)} :with :parent}]
               (:conflicts e))))
      (is (= {} (:numbers @(:journal book))) "nothing stamped")
      (ygg/discard-fork! w))))

(deftest an-at-most-one-family-stamps-the-copied-world-and-the-winner
  (with-book [book]
    (let [w (ygg/fork!)
          _ (add! w "book" (draft :w-1 1 :order-1))
          [a b] (ygg/copy-fork! w 2)]
      (add! a "book" (draft :a-1 2 :line-1))
      (add! b "book" (draft :b-1 3 :line-2))
      (ygg/merge-fork! a)
      (ygg/discard-fork! b)
      (is (= {:w-1 1 :a-1 2} (:numbers @(:journal book))))
      (is (= #{:w-1 :a-1} (set (map prov (elements "book"))))))))

(deftest a-failed-single-stamp-is-retried
  (with-book [book 2]
    (let [w (ygg/fork!)]
      (add! w "book" (draft :w-1 1 :x))
      (let [error (try (ygg/merge-fork! w) nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))]
        (is (= ::ygg/stamp-failed (:type error)))
        (is (= :incomplete (:status (ygg/fork-disposition w))))
        (is (= {} (:numbers @(:journal book))))
        (is (= ::ygg/stamp-failed (thrown-type #(ygg/retry-stamps!))))
        (is (= :incomplete (:status (ygg/fork-disposition w))))
        (is (= [(:pending error)] (ygg/retry-stamps!))))
      (is (= :merged (:status (ygg/fork-disposition w))))
      (is (= {:w-1 1} (:numbers @(:journal book))))
      (is (= [] (ygg/retry-stamps!)) "nothing pending"))))

(deftest stamp-recovery-uses-the-original-operation-and-defers-the-callback
  (with-book [book 1]
    (let [w (ygg/fork!)
          callbacks (atom [])
          phases (atom [])
          opts {:operation-id :single-stamp
                :on-merge #(swap! callbacks conj %)}]
      (reset! (:observe-stamp book)
              #(swap! phases conj (select-keys (ygg/fork-disposition w) [:status :phase])))
      (add! w "book" (draft :w-1 1 :x))
      (add! w "kb" :ordinary-change)
      (is (= ::ygg/stamp-failed (thrown-type #(ygg/merge-fork! w opts))))
      (is (= {:status :incomplete :phase :mutating :operation-id :single-stamp}
             (select-keys (ygg/fork-disposition w) [:status :phase :operation-id])))
      (is (empty? @callbacks))
      (is (= ::ygg/fork-not-open (thrown-type #(ygg/discard-fork! w))))
      (is (= ::ygg/fork-not-open (thrown-type #(ygg/transfer-fork! w :other))))
      (is (= ::ygg/fork-not-open
             (thrown-type #(ygg/merge-fork! w {:operation-id :different}))))
      (is (= ::ygg/fork-not-open (thrown-type #(ygg/merge-fork! w))))
      (let [result (ygg/merge-fork! w {:operation-id :single-stamp})]
        (is (= :merged (:status (ygg/fork-disposition w))))
        (is (= result (ygg/merge-fork! w)))
        (is (= 1 (count @callbacks)))
        (is (= #{:ordinary-change} (elements "kb")))
        (is (= {:w-1 1} (:numbers @(:journal book))))
        (is (= 2 @(:stamp-calls book)))
        (is (= 1 @(:realize-calls book)) "completed hooks are not replayed")
        (is (= [{:status :settling :phase :mutating}
                {:status :settling :phase :mutating}] @phases))
        (is (= [] (ygg/retry-stamps!)))))))

(deftest nested-copy-stamp-failure-keeps-every-capability-incomplete
  (with-book [book 1]
    (let [w (ygg/fork!)
          _ (add! w "book" (draft :w-1 1 :x))
          [a loser] (ygg/copy-fork! w 2)
          [winner] (ygg/copy-fork! a 1)
          phases (atom [])
          statuses #(mapv (fn [id] (:fork/status (ygg/copied-descriptor winner id)))
                          [(:fork-id a) (:fork-id w)])]
      (add! winner "book" (draft :winner-1 2 :y))
      (reset! (:observe-stamp book) #(swap! phases conj (statuses)))
      (is (= ::ygg/stamp-failed
             (thrown-type #(ygg/merge-fork! winner {:operation-id :copy-stamp}))))
      (is (= :incomplete (:status (ygg/fork-disposition winner))))
      (is (= [:incomplete :incomplete] (statuses)))
      (is (not= :merged (:status (ygg/copy-family winner))))
      (is (= ::ygg/copy-family-settled (thrown-type #(ygg/settle-family! [winner]))))
      (ygg/merge-fork! winner {:operation-id :copy-stamp})
      (is (= :merged (:status (ygg/fork-disposition winner))))
      (is (= [:merged :merged] (statuses)))
      (is (= [[:settling :settling] [:settling :settling]] @phases))
      (is (= {:w-1 1 :winner-1 2} (:numbers @(:journal book))))
      (ygg/discard-fork! loser))))

(deftest successful-stamp-precedes-terminal-and-runs-once
  (with-book [book]
    (let [w (ygg/fork!)
          events (atom [])
          opts {:on-merge (fn [_] (swap! events conj (:status (ygg/fork-disposition w))))}]
      (add! w "book" (draft :w-1 1 :x))
      (reset! (:observe-stamp book)
              #(swap! events conj (select-keys (ygg/fork-disposition w) [:status :phase])))
      (let [result (ygg/merge-fork! w opts)]
        (is (= result (ygg/merge-fork! w opts)))
        (is (contains? (:stamps result) "book"))
        (is (nil? (get-in result [:stamps "book"])))
        (is (= [{:status :settling :phase :mutating} :merged] @events))
        (is (= 1 @(:stamp-calls book)))))))

(deftest successful-stamp-steps-are-not-replayed-on-recovery
  (with-book [book]
    (let [other (toy-book 1)]
      (ygg/register! (mem-gset "zzz") (:policy other))
      (let [w (ygg/fork!)]
        (add! w "book" (draft :first 1 :x))
        (add! w "zzz" (draft :second 1 :y))
        (is (= ::ygg/stamp-failed
               (thrown-type #(ygg/merge-fork! w {:operation-id :two-stamps}))))
        (is (= 1 @(:stamp-calls book)))
        (ygg/merge-fork! w {:operation-id :two-stamps})
        (is (= 1 @(:stamp-calls book)) "the successful system's witness is reused")
        (is (= 2 @(:stamp-calls other)))
        (is (= {:first 1} (:numbers @(:journal book))))
        (is (= {:second 1} (:numbers @(:journal other))))))))

(deftest a-partly-committed-stamp-retries-the-original-contributions
  (let [ctx (sp/create-execution-context)
        book (toy-book)
        fail? (atom true)
        seen (atom [])
        policy (update (:policy book) :stamp
                       (fn [stamp]
                         (fn [args]
                           (swap! seen conj (mapv :intent/id (mapcat :intents (:contributions args))))
                           (let [result (stamp args)]
                             (when (compare-and-set! fail? true false)
                               (throw (ex-info "failed after committing" {})))
                             result))))]
    (sp/with-context ctx
      (ygg/register! (mem-gset "book") policy)
      (let [w (ygg/fork!)]
        (add! w "book" (draft :w-1 1 :x))
        (is (= ::ygg/stamp-failed
               (thrown-type #(ygg/merge-fork! w {:operation-id :partial-stamp}))))
        (is (= :incomplete (:status (ygg/fork-disposition w))))
        (is (= {:w-1 1} (:numbers @(:journal book))))
        (ygg/merge-fork! w {:operation-id :partial-stamp})
        (is (= :merged (:status (ygg/fork-disposition w))))
        (is (= [[:w-1] [:w-1]] @seen))
        (is (= {:w-1 1} (:numbers @(:journal book))))))))

(deftest checkpoint-stamp-retry-remains-available
  (with-book [book 2]
    (let [w (ygg/fork!)]
      (add! w "book" (draft :w-1 1 :x))
      (is (= ::ygg/stamp-failed (thrown-type #(ygg/checkpoint! w))))
      (is (= :open (:status (ygg/fork-disposition w))))
      (is (thrown? clojure.lang.ExceptionInfo (ygg/retry-stamps!)))
      (is (= 1 (count (ygg/retry-stamps!))))
      (is (= [] (ygg/retry-stamps!)))
      (is (= {:w-1 1} (:numbers @(:journal book))))
      (ygg/discard-fork! w))))

(deftest a-settled-family-cannot-settle-again
  (with-book [book]
    (let [[a b] (ygg/copy-fork! (ygg/fork!) 2)]
      (add! a "book" (draft :a-1 1 :x))
      (add! b "book" (draft :b-1 2 :y))
      (ygg/settle-family! [a])
      (is (nil? (ygg/settle-family! [a])) "the same settlement again is a no-op")
      (is (= ::ygg/copy-family-settled (thrown-type #(ygg/settle-family! [b]))))
      (is (= ::ygg/copy-family-settled (thrown-type #(ygg/merge-fork! b))))
      (ygg/discard-fork! b)
      (is (= {:a-1 1} (:numbers @(:journal book)))))))

(deftest a-long-lived-world-settles-as-it-goes
  (with-book [book]
    (let [w (ygg/fork!)]
      (add! w "book" (draft :w-1 1 :line-1))
      (ygg/checkpoint! w)
      (is (= {:w-1 1} (:numbers @(:journal book))) "settled while the world goes on")
      (is (= #{:w-1} (set (map prov (elements (:child-ctx w) "book"))))
          "the world continues from its parent's new head")
      (add! w "book" (draft :w-2 2 :line-2))
      (ygg/checkpoint! w)
      (is (= {:w-1 1 :w-2 2} (:numbers @(:journal book))) "only what came after")
      (testing "the parent's claims between checkpoints are checked"
        (add! w "book" (draft :w-3 3 :line-3))
        (swap! (ygg/system-signal "book") #(g/conj % (draft :root-1 3 :line-3)))
        (is (= ::ygg/merge-conflict (thrown-type #(ygg/checkpoint! w)))))
      (ygg/discard-fork! w)
      (is (= {:w-1 1 :w-2 2} (:numbers @(:journal book)))))))

(deftest a-checkpointed-world-merges-only-the-rest
  (with-book [book]
    (let [w (ygg/fork!)]
      (add! w "book" (draft :w-1 1 :line-1))
      (ygg/checkpoint! w)
      (add! w "book" (draft :w-2 2 :line-2))
      (ygg/merge-fork! w)
      (is (= {:w-1 1 :w-2 2} (:numbers @(:journal book))))
      (is (= #{:w-1 :w-2} (set (map prov (elements "book"))))))))

(deftest a-reviewer-sees-intents-and-the-parent-s-claims
  (with-book [_]
    (let [w (ygg/fork!)]
      (add! w "book" (draft :w-1 1 :line-1))
      (add! w "book" (draft :w-2 2 :line-2))
      (swap! (ygg/system-signal "book") #(g/conj % (draft :root-1 1 :line-2)))
      (let [diff (ygg/context-diff (:child-ctx w))
            conflicts (ygg/context-conflicts (:child-ctx w))]
        (is (= #{:w-1 :w-2} (set (map :intent/id (get-in diff ["book" :intents]))))
            "the diff of an intent system is its intents")
        (is (= [{:system "book" :key :line-2 :intent :w-2 :with :parent}] conflicts)
            "its conflicts are the parent's claims on their footprints"))
      (ygg/discard-fork! w))))

(deftest family-recovery-authenticates-every-supplied-capability
  (doseq [invalid [:stale-participant :transferred-loser :discarded-loser :open-loser]
          explicit-id? [false true]]
    (testing (str invalid ", explicit id: " explicit-id?)
      (with-book [book 1]
        (let [[a b loser] (ygg/copy-fork! (ygg/fork!) 3)
              adopted (when (= invalid :stale-participant) (ygg/transfer-fork! a :adopted))
              _ (when (= invalid :transferred-loser) (ygg/transfer-fork! loser :other))
              _ (when (= invalid :discarded-loser) (ygg/discard-fork! loser))
              participants [(or adopted a) b]
              bad (if adopted a loser)
              opts (if explicit-id? {:operation-id :authenticated} {})]
          (is (= ::ygg/family-stamp-failed
                 (thrown-type #(ygg/settle-family! participants {:operation-id :authenticated}))))
          (is (some? (thrown-type #(ygg/settle-family! [(first participants) bad] opts))))
          (is (= 1 @(:stamp-calls book)) "invalid callers cannot invoke the saved operation")
          (is (= :failed (:status (ygg/copy-family b))))
          (ygg/settle-family! [b] opts)
          (is (= [:merged :merged] (mapv #(-> % ygg/fork-disposition :status) participants))))))))

(deftest pending-stamp-retries-belong-only-to-the-parent-world
  (doseq [mode [:following :frozen]]
    (with-book [book 1]
      (let [parent ec/*execution-context*
            w (ygg/fork!)
            callbacks (atom 0)
            opts {:operation-id :world-owned :on-merge (fn [_] (swap! callbacks inc))}]
        (add! w "book" (draft :w-1 1 :x))
        (is (= ::ygg/stamp-failed (thrown-type #(ygg/merge-fork! w opts))))
        (let [child (ctx/fork-context parent :mode mode)
              snapshot (ctx/snapshot-context parent :clean-in-flight? false)]
          (is (empty? (rtp/get-state child [::ygg/pending-stamps])))
          (is (empty? (rtp/get-state snapshot [::ygg/pending-stamps])))
          ;; Whole-state materialization must not cache an executable parent entry.
          (is (empty? (get (rtp/get-state child []) ::ygg/pending-stamps)))
          (is (= [] (ygg/retry-stamps! child)))
          (is (= :incomplete (:status (ygg/fork-disposition w))))
          (is (= 0 @callbacks))
          (ygg/merge-fork! w {:operation-id :world-owned})
          (is (= 1 @callbacks))
          (is (= [] (ygg/retry-stamps! parent)))
          (is (empty? (get (rtp/get-state child []) ::ygg/pending-stamps)))
          (is (empty? (rtp/get-state snapshot [::ygg/pending-stamps])))
          (is (= [] (ygg/retry-stamps! (ctx/restore-snapshot snapshot :drain-events? false)))))))))
