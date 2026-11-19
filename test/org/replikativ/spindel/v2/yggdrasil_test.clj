(ns org.replikativ.spindel.v2.yggdrasil-test
  "The yggdrasil-on-v2 layer (port step 5a, §2 of the step-5 design):
   recorded bases and lazy branches, unmanaged forks (F10), merge and
   discard (F3-F6), the journal (F6a), immediate parents (F4), closing
   (F11), child-only systems (F8) and checkpoint bases."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [datahike.api :as d]
            [geschichte.query :as query]
            [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.ygg-support :as s
             :refer [caught close-world! dh-system done! eventually gs-system put! root st
                     text-in val-in with-stores write!]]
            [org.replikativ.spindel.v2.yggdrasil :as ygg]
            [yggdrasil.protocols :as yp]))

(deftest a-fork-records-a-frozen-base-and-branches-on-first-resolution
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])]
      (put! kb :a "a")
      (let [snap (str (yp/snapshot-id kb))
            f (ygg/fork! w {})
            c (:world f)]
        (put! kb :b "b")
        (testing "the base is the parent's snapshot at the fork"
          (is (= {"kb" {:base {:snapshot snap}}} (ygg/locators f)))
          (is (= {"kb" snap} (ygg/snapshot-ids c))))
        (testing "view reads the base and never branches"
          (let [db (ygg/view c "kb")]
            (is (= "a" (val-in db :a)))
            (is (nil? (val-in db :b))))
          (is (nil? (get-in (ygg/locators f) ["kb" :branch])) "NEGATIVE: view branched"))
        (testing "the first system call branches at the base"
          (let [h (ygg/system c "kb")]
            (is (keyword? (get-in (ygg/locators f) ["kb" :branch])))
            (is (identical? h (ygg/system c "kb")) "later calls return the same handle")
            (is (identical? h (ygg/view c "kb")) "view returns the fork's handle once it has one")
            (is (= "a" (val-in h :a)))
            (is (nil? (val-in h :b)) "frozen: the parent's later write is not seen")
            (put! h :c "c")
            (is (nil? (val-in kb :c)) "isolated: the parent does not see the fork's write")))
        (ygg/discard! f {})
        (done! w)))))

(deftest unmanaged-forks-view-their-managed-ancestors-bases
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])]
      (put! kb :a "a")
      (let [f (ygg/fork! w {})
            c (:world f)
            _ (put! kb :b "b")
            h (ygg/system c "kb")
            _ (put! h :c "c")
            u (v2/fork! c)
            uu (v2/fork! u)
            r (v2/fork! w)]
        (testing "an engine fork of a layer fork is unmanaged"
          (is (identical? c (ygg/managed-ancestor u)))
          (is (identical? c (ygg/managed-ancestor uu)))
          (is (not (ygg/fork? u))))
        (testing "view reads the nearest managed ancestor's recorded base, frozen"
          (doseq [x [u uu]]
            (let [db (ygg/view x "kb")]
              (is (= "a" (val-in db :a)))
              (is (nil? (val-in db :b)) "the parent's write after the fork")
              (is (nil? (val-in db :c)) "NEGATIVE: the ancestor's live handle was read"))))
        (testing "system, registration and layer forks are refused there"
          (is (= ::ygg/unmanaged-world (caught #(ygg/system u "kb"))))
          (is (= ::ygg/unmanaged-world (caught #(ygg/register! u (dh-system "x") {}))))
          (is (= ::ygg/unmanaged-world (caught #(ygg/fork! u {})))))
        (testing "an engine fork of the registering world reads its snapshot"
          (is (identical? w (ygg/managed-ancestor r)))
          (is (= "b" (val-in (ygg/view r "kb") :b)))
          (is (= ::ygg/unmanaged-world (caught #(ygg/system r "kb")))))
        (testing "a world with no managed ancestor resolves nothing"
          (let [fresh (v2/world)]
            (is (nil? (ygg/managed-ancestor fresh)))
            (is (= ::ygg/no-managed-ancestor (caught #(ygg/view fresh "kb"))))
            (is (= ::ygg/unknown-system (caught #(ygg/system fresh "kb"))))
            (done! fresh)))
        (ygg/discard! f {})
        (done! w)))))

(deftest merge-stops-prechecks-merges-closes-then-runs-the-hook
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          log (atom [])
          f (ygg/fork! w {:meta {:room :r1}})
          c (:world f)
          ticks (atom 0)]
      (binding [v2/*world* c]
        (task (loop [] (v2/sleep 10) (swap! ticks inc) (recur))))
      (put! (ygg/system c "kb") :x "child")
      (let [res (ygg/merge! f {:stop (fn [] (swap! log conj [:stop (v2/sealed? c)]) :stopped)
                               :restart (fn [] (swap! log conj :restart))
                               :precheck (fn [m] (swap! log conj [:precheck (:plan m)]) true)
                               :guard (fn [sid _] (swap! log conj [:guard sid]) true)
                               :on-merge (fn [p] (swap! log conj [:hook p (v2/complete? c)]))})]
        (is (= [[:stop true] [:precheck ["kb"]] [:guard "kb"]
                [:hook {:fork/id (:id f) :meta {:room :r1} :merged ["kb"] :adopted {}} true]]
               @log))
        (is (= :merged (:status res)))
        (is (= :completed (:hook-status res)))
        (is (= "child" (val-in kb :x)) "the store landed in the parent")
        (is (v2/complete? c) "the close released and joined the fork")
        (is (= ::ygg/settled (caught #(ygg/discard! f {}))) "affine: settled once")
        (is (= :merged (:status (ygg/merge! f {}))) "the same settlement again is a no-op"))
      (done! w))))

(deftest discard-drops-the-branches-and-runs-the-hook
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          f (ygg/fork! w {:meta {:room :r2}})
          c (:world f)
          h (ygg/system c "kb")
          branch (get-in (ygg/locators f) ["kb" :branch])
          hook (atom nil)]
      (put! h :x "child")
      (is (contains? (yp/branches kb) branch))
      (let [res (ygg/discard! f {:on-discard #(reset! hook %)})]
        (is (= :discarded (:status res)))
        (is (= {:fork/id (:id f) :meta {:room :r2} :dropped {"kb" nil} :reason :discarded} @hook))
        (is (nil? (val-in kb :x)))
        (is (not (contains? (yp/branches kb) branch)) "NEGATIVE: the overlay branch was kept")
        (is (v2/complete? c))
        (is (= ::ygg/settled (caught #(ygg/merge! f {})))))
      (done! w))))

(deftest a-precheck-refusal-unseals-and-restarts-the-live-fork
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          f (ygg/fork! w {})
          c (:world f)
          log (atom [])]
      (put! (ygg/system c "kb") :x "child")
      (testing "the caller's precheck refuses"
        (is (= ::ygg/refused
               (caught #(ygg/merge! f {:stop (fn [] (swap! log conj :stop))
                                       :restart (fn [] (swap! log conj [:restart (v2/sealed? c)]))
                                       :precheck (constantly false)}))))
        (is (= [:stop [:restart false]] @log) "unsealed, then restarted")
        (is (= :open (st f)))
        (is (some? (:last-error (ygg/status f))))
        (is (not (v2/sealed? c)))
        (is (not (v2/complete? c)) "the fork's world survives")
        (is (= 2 (v2/value (binding [v2/*world* c] (task (+ 1 1))) 5000 ::timeout)) "the fork runs work again")
        (is (nil? (val-in kb :x))))
      (testing "a conflict refuses, :force? merges"
        (put! kb :x "parent")
        (let [cs (ygg/conflicts f)]
          (is (seq cs))
          (is (every? #(= "kb" (:system %)) cs) "a flat seq tagged :system"))
        (is (= ::ygg/refused (caught #(ygg/merge! f {}))))
        (is (= :open (st f)))
        (is (= "child" (val-in (ygg/system c "kb") :x)))
        (is (= :merged (:status (ygg/merge! f {:force? true}))))
        (is (= "child" (val-in kb :x))))
      (done! w))))

(deftest a-refusal-inside-the-adapter-merge-with-nothing-done-restarts
  (with-stores
    (let [repo (gs-system "repo")
          w (root [repo])
          f (ygg/fork! w {})
          c (:world f)
          restarted (atom 0)]
      (write! (ygg/system c "repo") "child.txt" "child")
      (write! repo "dirty.txt" "dirty" false)
      (let [e (try (ygg/merge! f {:restart #(swap! restarted inc)}) nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (= ::ygg/refused (:type (ex-data e))))
        (is (re-find #"dirty" (ex-message (ex-cause e))) "geschichte refused a dirty parent inside merge-down!"))
      (is (= 1 @restarted))
      (is (= :open (st f)))
      (is (empty? (:done (ygg/status f))))
      (is (not (v2/sealed? c)))
      (is (nil? (text-in repo "child.txt")))
      (testing "after the parent is clean the merge lands"
        (write! repo "dirty.txt" "dirty")
        (is (= :merged (:status (ygg/merge! f {}))))
        (is (= "child" (text-in repo "child.txt"))))
      (done! w))))

(deftest a-stop-miss-leaves-the-fork-open-sealed-and-stopped
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          f (ygg/fork! w {})
          c (:world f)
          restarted (atom 0)]
      (put! (ygg/system c "kb") :x "child")
      (let [e (try (ygg/merge! f {:stop (constantly {:status :stuck :pending [:turn]})
                                  :restart #(swap! restarted inc)})
                   nil (catch clojure.lang.ExceptionInfo e e))]
        (is (= [::ygg/refused :stuck] ((juxt :type :reason) (ex-data e)))))
      (is (= :open (st f)))
      (is (= {:status :stuck :pending [:turn]} (:stop-report (ygg/status f))))
      (is (v2/sealed? c) "NEGATIVE: unsealed after a stop miss")
      (is (zero? @restarted))
      (is (nil? (val-in kb :x)))
      (testing "a later merge stops again"
        (is (= :merged (:status (ygg/merge! f {:stop (constantly :ok)}))))
        (is (= "child" (val-in kb :x))))
      (done! w))))

(deftest the-plan-orders-by-merge-rank-then-sid-and-child-only-last
  (with-stores
    (let [systems {"a-data" 2 "b-repo" 0 "c-book" 1 "d-kb" 2 "e-msgs" nil}
          w (v2/world)
          _ (doseq [[sid rank] systems]
              (ygg/register! w (dh-system sid) {:meta (when rank {:merge-rank rank})}))
          f (ygg/fork! w {})
          c (:world f)
          order (atom [])]
      (doseq [sid (keys systems)] (put! (ygg/system c sid) :x sid))
      (ygg/register! c (dh-system "aa-child") {:meta {:merge-rank 0}})
      (let [res (ygg/merge! f {:guard (fn [sid _] (swap! order conj sid) true)})]
        (is (= ["b-repo" "c-book" "a-data" "d-kb" "e-msgs" "aa-child"] @order (:plan res)))
        (is (= :merged (:status res))))
      (done! w))))

(deftest a-mid-plan-failure-is-incomplete-and-recover-completes-it
  (with-stores
    (let [one (dh-system "one")
          two (dh-system "two")
          w (root [one {:meta {:merge-rank 0}}] [two {:meta {:merge-rank 1}}])
          f (ygg/fork! w {})
          c (:world f)
          fail? (atom true)
          hooks (atom 0)]
      (put! (ygg/system c "one") :x "1")
      (put! (ygg/system c "two") :x "2")
      (is (= ::ygg/incomplete
             (caught #(ygg/merge! f {:guard (fn [sid _]
                                              (when (and (= "two" sid) @fail?)
                                                (throw (ex-info "frontier moved" {}))))
                                     :on-merge (fn [_] (swap! hooks inc))}))))
      (is (= :incomplete (st f)))
      (is (= #{"one"} (:done (ygg/status f))))
      (is (= "1" (val-in one :x)))
      (is (nil? (val-in two :x)))
      (is (v2/sealed? c) "the fork stays stopped")
      (is (= ::ygg/fork-not-open (caught #(ygg/merge! f {}))))
      (reset! fail? false)
      (let [res (ygg/recover! f)]
        (is (= :merged (:status res)))
        (is (= "2" (val-in two :x)))
        (is (= 1 @hooks)))
      (done! w))))

(deftest a-hook-failure-keeps-the-outcome-and-recover-reruns-it
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          f (ygg/fork! w {})
          calls (atom 0)]
      (put! (ygg/system (:world f) "kb") :x "child")
      (let [res (ygg/merge! f {:on-merge (fn [_] (when (= 1 (swap! calls inc))
                                                   (throw (ex-info "row store down" {}))))})]
        (is (= [:merged :failed] ((juxt :status :hook-status) res)))
        (is (= "child" (val-in kb :x))))
      (is (= [:merged :completed] ((juxt :status :hook-status) (ygg/recover! f))))
      (is (= 2 @calls))
      (is (= :completed (:hook-status (ygg/recover! f))) "a completed hook does not run again")
      (is (= 2 @calls))
      (done! w))))

(deftest the-journal-sees-creation-and-every-status-plan-and-done-change
  (with-stores
    (let [kb (dh-system "kb")
          msgs (dh-system "msgs")
          w (root [kb {:meta {:merge-rank 0}}] [msgs {:meta {:merge-rank 1}}])
          rows (atom [])
          f (ygg/fork! w {:meta {:room :r} :journal #(swap! rows conj %)})
          c (:world f)]
      (let [created (first @rows)]
        (is (= [:created :open] ((juxt :event :status) created)))
        (is (= (:id f) (:fork/id created)))
        (is (= #{"kb" "msgs"} (set (keys (:locators created)))))
        (is (every? (comp :snapshot :base) (vals (:locators created)))))
      (put! (ygg/system c "kb") :x "k")
      (put! (ygg/system c "msgs") :x "m")
      (is (= [:created :branched :branched] (mapv :event @rows)))
      (is (= #{"kb" "msgs"} (set (keep (fn [[sid l]] (when (:branch l) sid)) (:locators (last @rows))))))
      (ygg/merge! f {})
      (is (= [[:created :open nil #{}]
              [:branched :open nil #{}]
              [:branched :open nil #{}]
              [:claimed :settling nil #{}]
              [:plan :settling ["kb" "msgs"] #{}]
              [:done :settling ["kb" "msgs"] #{"kb"}]
              [:done :settling ["kb" "msgs"] #{"kb" "msgs"}]
              [:cleaned :settling ["kb" "msgs"] #{"kb" "msgs"}]
              [:cleaned :settling ["kb" "msgs"] #{"kb" "msgs"}]
              [:merged :merged ["kb" "msgs"] #{"kb" "msgs"}]]
             (mapv (juxt :event :status :plan :done) @rows)))
      (is (every? #(= {:room :r} (:meta %)) @rows))
      (done! w))))

(deftest a-fork-of-a-fork-merges-into-its-immediate-parent
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          f1 (ygg/fork! w {})
          f2 (ygg/fork! (:world f1) {})]
      (put! (ygg/system (:world f2) "kb") :x "inner")
      (testing "a parent with an unsettled fork refuses to merge"
        (is (= ::ygg/open-children (caught #(ygg/merge! f1 {}))))
        (is (= :open (st f1))))
      (testing "the inner fork lands in its parent, not the root"
        (is (= :merged (:status (ygg/merge! f2 {}))))
        (is (= "inner" (val-in (ygg/system (:world f1) "kb") :x)))
        (is (nil? (val-in kb :x)) "NEGATIVE: merged past the immediate parent"))
      (testing "then the parent lands in the root"
        (is (= :merged (:status (ygg/merge! f1 {}))))
        (is (= "inner" (val-in kb :x))))
      (done! w))))

(deftest a-discard-cascades-to-unsettled-forks
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          f1 (ygg/fork! w {})
          hook (atom nil)
          f2 (ygg/fork! (:world f1) {:on-discard #(reset! hook %)})]
      (put! (ygg/system (:world f2) "kb") :x "inner")
      (is (= :discarded (:status (ygg/discard! f1 {}))))
      (is (= :discarded (st f2)))
      (is (= :parent-discarded (:reason @hook)))
      (is (v2/complete? (:world f2)))
      (done! w))))

(deftest closing-a-fork-keeps-it-unsettled-and-reviewable
  (with-stores
    (let [kb (dh-system "kb")
          data (dh-system "data")
          w (root [kb] [data])
          f (ygg/fork! w {})
          c (:world f)]
      (put! (ygg/system c "kb") :x "child")
      (let [head (str (yp/snapshot-id (ygg/system c "kb")))
            base (get-in (ygg/locators f) ["data" :base :snapshot])]
        (close-world! c)
        (Thread/sleep 100)
        (is (= ::s/released (try (v2/world-state c) (catch clojure.lang.ExceptionInfo e (when (:spindel/released (ex-data e)) ::s/released))))
            "the world's state is gone")
        (is (= :open (st f)) "NEGATIVE: the close settled the fork")
        (testing "review reads host-side data only (P3)"
          (is (= #{"kb"} (set (keys (ygg/diff f)))))
          (is (= {"kb" head "data" base} (ygg/snapshot-ids c)))
          (is (= [:open nil] ((juxt :status :hook-status) (ygg/status f))))
          (is (= #{"kb" "data"} (set (keys (ygg/systems c)))))
          (is (= "child" (val-in (ygg/view c "kb") :x)))
          (put! kb :x "parent")
          (is (every? #(= "kb" (:system %)) (ygg/conflicts f)))
          (is (seq (ygg/conflicts f)))))
      (testing "a closed fork merges without a stop or close (a Run world after its join)"
        (let [log (atom [])]
          (is (= :merged (:status (ygg/merge! f {:force? true
                                                 :stop #(swap! log conj :stop)
                                                 :close #(swap! log conj :close)}))))
          (is (empty? @log))
          (is (= "child" (val-in kb :x)))))
      (done! w))))

(deftest the-end-of-the-parents-world-discards-its-unsettled-forks
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          hooks (atom [])
          open (ygg/fork! w {:on-discard #(swap! hooks conj [:open (:reason %)])})
          closed (ygg/fork! w {:on-discard #(swap! hooks conj [:closed (:reason %)])})
          merged (ygg/fork! w {})]
      (put! (ygg/system (:world open) "kb") :x "open")
      (close-world! (:world closed))
      (ygg/merge! merged {})
      (done! w)
      (is (eventually #(and (= :discarded (st open)) (= :discarded (st closed)))) "NEGATIVE: forks outlived their parent")
      (is (= #{[:open :parent-ended] [:closed :parent-ended]} (eventually #(when (= 2 (count @hooks)) (set @hooks)))))
      (is (= :merged (st merged)))
      (is (eventually #(nil? (ygg/fork-of (:world open)))) "no holder of the lineage remains"))))

(deftest a-child-only-system-is-adopted-on-merge-and-cleaned-on-discard
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])]
      (testing "merge adopts it with its meta"
        (let [f (ygg/fork! w {})
              data (dh-system "data")
              hook (atom nil)]
          (ygg/register! (:world f) data {:meta {:grant {:db :data}}})
          (put! data :x "fresh")
          (is (= {:base nil :child-only true :meta {:grant {:db :data}}} (get (ygg/locators f) "data")))
          (ygg/merge! f {:on-merge #(reset! hook %)})
          (is (= {"data" {:grant {:db :data}}} (:adopted @hook)))
          (is (= {:grant {:db :data}} (get (ygg/systems w) "data")))
          (is (identical? data (ygg/system w "data")))))
      (testing "discard runs its cleanup policy"
        (let [f (ygg/fork! w {})
              scratch (dh-system "scratch")
              cleaned (atom nil)
              hook (atom nil)]
          (ygg/register! (:world f) scratch {:meta {:grant :g} :policy {:cleanup #(reset! cleaned %)}})
          (ygg/discard! f {:on-discard #(reset! hook %)})
          (is (= {:sid "scratch" :handle scratch :meta {:grant :g}} @cleaned))
          (is (= {"scratch" {:grant :g}} (:dropped @hook)))
          (is (not (contains? (ygg/systems w) "scratch")))))
      (done! w))))

(deftest registration-and-resolution-refusals
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          f (ygg/fork! w {})]
      (is (= ::ygg/already-registered (caught #(ygg/register! w kb {}))))
      (is (= ::ygg/inherited-system (caught #(ygg/unregister! (:world f) "kb"))))
      (is (= ::ygg/not-host (caught #(v2/value (binding [v2/*world* w] (task (ygg/system w "kb"))) 5000 ::timeout)))
          "refused in a body (B7)")
      (close-world! (:world f))
      (ygg/discard! f {})
      (is (= ::ygg/fork-not-open (caught #(ygg/system (:world f) "kb")))
          "a settled fork branches nothing")
      (done! w))))

(deftest a-checkpoint-base
  (with-stores
    (let [repo (gs-system "repo")
          w (root [repo])
          conn (:conn repo)]
      (write! repo "kept.txt" "at checkpoint")
      (let [cp {:version 1 :kind :datahike :commit (d/commit-id @conn)
                :source {:store (get-in @conn [:config :store :id])
                         :repository (:geschichte.repo/id (query/repository @conn))}}]
        (write! repo "later.txt" "after")
        (let [f (ygg/fork! w {:bases {"repo" {:checkpoint cp}}})
              c (:world f)]
          (is (= {"repo" {:base {:checkpoint cp}}} (ygg/locators f)))
          (is (= ::ygg/no-view (caught #(ygg/view c "repo"))))
          (let [h (ygg/system c "repo")]
            (is (= "at checkpoint" (text-in h "kept.txt")))
            (is (nil? (text-in h "later.txt"))))
          (is (= :discarded (:status (ygg/discard! f {}))))
          (is (= ::ygg/invalid-base (caught #(ygg/fork! w {:bases {"repo" {:checkpoint (atom 1)}}}))))))
      (done! w))))
