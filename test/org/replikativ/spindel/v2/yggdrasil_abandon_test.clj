(ns org.replikativ.spindel.v2.yggdrasil-abandon-test
  "`abandon!` (F11/F6a, daemon stop): a fork is forgotten without settling
   it; its branches stay for the caller's boot cleanup and the end of the
   parent's world no longer discards it. `:locate` names a branched overlay
   in `locators`."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.ygg-support :as s
             :refer [caught close-world! dh-system done! eventually put! root st with-stores]]
            [org.replikativ.spindel.v2.yggdrasil :as ygg]
            [yggdrasil.protocols :as yp]))

(deftest abandon-leaves-branches-runs-no-hooks-and-escapes-the-parent-end
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          events (atom [])
          hooks (atom [])
          f (ygg/fork! w {:journal #(swap! events conj %)
                          :on-discard #(swap! hooks conj %)})
          c (:world f)]
      (put! (ygg/system c "kb") :x "child")
      (let [branch (get-in (ygg/locators f) ["kb" :branch])]
        (close-world! c)
        (is (= :abandoned (:status (ygg/abandon! f))))
        (is (contains? (yp/branches kb) branch) "NEGATIVE: abandon cleaned the branch")
        (let [last-event (last @events)]
          (is (= :abandoned (:event last-event)))
          (is (= branch (get-in last-event [:locators "kb" :branch])) "the journal keeps the locators"))
        (testing "settlement refuses an abandoned fork"
          (is (= ::ygg/fork-not-open (caught #(ygg/merge! f {}))))
          (is (= ::ygg/fork-not-open (caught #(ygg/discard! f {})))))
        (done! w)
        (Thread/sleep 100)
        (is (= :abandoned (st f)) "NEGATIVE: the parent's end discarded it")
        (is (empty? @hooks) "no hook ran")
        (is (contains? (yp/branches kb) branch) "the branch is left for boot cleanup")
        (is (= 1 (count (filter #(= :abandoned (:event %)) @events))) "journaled once")))))

(deftest abandon-takes-unsettled-forks-of-the-fork-with-it
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          events (atom [])
          f (ygg/fork! w {:journal #(swap! events conj [:f (:event %)])})
          g (ygg/fork! (:world f) {:journal #(swap! events conj [:g (:event %)])})]
      (put! (ygg/system (:world g) "kb") :x "grandchild")
      ;; daemon stop: abandon first, then close the worlds. Closing f's world
      ;; first ends g's parent, and the parent-ended rule would discard g.
      (ygg/abandon! f)
      (is (= [:abandoned :abandoned] [(st f) (st g)]))
      (close-world! (:world g))
      (close-world! (:world f))
      (Thread/sleep 100)
      (is (= [[:g :abandoned] [:f :abandoned]] (filterv #(= :abandoned (second %)) @events))
          "the fork's forks first")
      (done! w)
      (Thread/sleep 100)
      (is (= [:abandoned :abandoned] [(st f) (st g)])))))

(deftest abandon-refuses-a-settled-fork
  (with-stores
    (let [kb (dh-system "kb")
          w (root [kb])
          f (ygg/fork! w {})]
      (ygg/discard! f {})
      (is (= ::ygg/settled (caught #(ygg/abandon! f))))
      (done! w))))

(deftest locate-names-a-branched-overlay
  (with-stores
    (let [kb (dh-system "kb")
          w (v2/world)
          _ (ygg/register! w kb {:policy {:locate (fn [{:keys [sid meta]}] {:workspace [sid (:kind meta)]})}
                                 :meta {:kind :repo}})
          f (ygg/fork! w {})]
      (is (= {:base (get-in (ygg/locators f) ["kb" :base])} (get (ygg/locators f) "kb"))
          "unbranched: the base only")
      (put! (ygg/system (:world f) "kb") :x "child")
      (is (= ["kb" :repo] (get-in (ygg/locators f) ["kb" :workspace])) "NEGATIVE: :locate ignored")
      (is (not (contains? (get (ygg/locators f) "kb") :branch)) ":locate replaces the default branch name")
      (ygg/discard! f {})
      (done! w))))
