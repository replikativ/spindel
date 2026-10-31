(ns org.replikativ.spindel.lifetime.fork-entry-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.cleanup :as cleanup]
            [org.replikativ.spindel.engine.kernel :as kernel]))

(def w [:w 0])
(def v [:w 1])
(def r [:spin 1])
(def source-ticket (cleanup/ticket w r))
(def child-ticket (cleanup/ticket v r))
(def child-cell [v r :cell])
(def fork-action {:t :t19 :w w :v v :k [:cap 0] :scope [:root w] :systems #{}})

(defn checked [before action]
  (let [{after :state :keys [refusal observation]} (m/attempt before action)]
    (is (nil? refusal) (pr-str [action refusal]))
    (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
    (is (empty? (inv/edge-check {:before before :action action :after after
                                 :refusal refusal :observation observation})) (pr-str action))
    after))

(defn entered-parked []
  (reduce checked (m/init-state {:slices? true :cps-exit? true})
          [{:t :t04 :w w :e :spin :mode :callback}
           {:t :slice-enter :w w :r r :th :worker}
           {:t :t02 :w w :scope r :e :cell :kind :signal :value :payload}
           ;; Real finalization entry/resume establishes nonzero history without
           ;; leaving an active cleanup participant to copy.
           {:t :finalization-wait :w w :th :worker}
           {:t :cleanup-deliver :n source-ticket :sequence 1 :value :prior}
           {:t :finalization-resume :w w :n source-ticket :th :worker}
           {:t :t05 :w w :r r :kind :await-once :debtor [:host :gate] :order 1}
           {:t :t38 :th :worker}]))

(defn rejects-injected-entry [before action after run]
  (let [corrupt (assoc-in after [:worlds (:v action) :runs run :cps-entered?] true)
        edge {:before before :action action :after corrupt}]
    (is (seq (inv/fork-entry-errors edge)))
    (is (some #(= :ForkEntry (:id %)) (inv/edge-check edge)))))

(deftest following-copy-preserves-history-without-copying-world-entry
  (let [before (entered-parked)
        copied (checked before fork-action)]
    (is (true? (:cps-entered? (m/run before w r))))
    (is (= :parked (:status (m/run before w r))))
    (is (= 1 (:finalization-sequence (m/run before w r))))
    (is (empty? (get-in before [:env :native])))
    (is (empty? (get-in before [:env :cleanup-cells])))
    (is (= (m/run before w r) (m/run copied w r)))
    (is (= :inherited (:status (m/run copied v r))))
    (is (not (contains? (m/run copied v r) :cps-entered?)))
    (is (= 1 (:finalization-sequence (m/run copied v r))))
    (is (= :payload (:result (m/ent copied v :cell))))
    (is (not-any? #(= v (:world %)) (vals (get-in copied [:env :threads]))))
    (rejects-injected-entry before fork-action copied r)
    ;; Both independent kernel storage representations must carry the same
    ;; newly unentered child rows, rather than dropping the comparison field.
    (doseq [cells? [false true]]
      (let [actual (kernel/restore before {:cells? cells?})]
        (kernel/step! actual fork-action)
        (is (= (select-keys copied [:worlds :env :caps :custody :serial :clocks])
               (select-keys (kernel/snapshot actual) [:worlds :env :caps :custody :serial :clocks])))))))

(deftest logical-child-resume-does-not-reserve-phantom-finally-work
  (let [copied (checked (entered-parked) fork-action)
        resumed (checked copied {:t :t06 :w v :o [:o 1] :value :resume})
        cancelled (checked resumed {:t :t11 :w v :r r})]
    (is (= :running (:status (m/run resumed v r))))
    (is (not (contains? (m/run resumed v r) :cps-entered?)))
    (is (nil? (m/run cancelled v r)))
    (is (nil? (get-in cancelled [:env :native child-ticket])))
    (is (empty? (get-in cancelled [:env :cleanup-cells])))
    (is (true? (m/join-ready? cancelled v [:root v])))
    (is (= (m/wr copied w) (m/wr cancelled w)))))

(deftest actual-child-entry-reserves-its-own-cell-and-physical-exit
  (let [copied (checked (entered-parked) fork-action)
        entered (reduce checked copied
                        [{:t :t06 :w v :o [:o 1] :value :resume}
                         {:t :slice-enter :w v :r r :th :child-worker}])
        cancelled (checked entered {:t :t11 :w v :r r})
        returned (checked cancelled {:t :t38 :th :child-worker})]
    (is (true? (:cps-entered? (m/run entered v r))))
    (is (= :unwinding (:status (m/run cancelled v r))))
    (is (= [r [:root v] v] (:anchor (m/run cancelled v r))))
    (is (= [r [:root v] v] (get-in cancelled [:env :native child-ticket :anchor])))
    (is (= #{child-ticket} (get-in cancelled [:env :cleanup-cells child-cell :holders])))
    (is (= :payload (get-in cancelled [:env :cleanup-cells child-cell :result])))
    (is (false? (m/join-ready? cancelled v [:root v])))
    (is (false? (m/join-ready? returned v [:root v])))
    (let [claimed (checked returned {:t :cleanup-claim :n child-ticket :th :cleaner})
          returning (checked claimed {:t :cleanup-return :th :cleaner})
          done (checked returning {:t :t38 :th :cleaner})]
      (is (false? (m/join-ready? returning v [:root v])))
      (is (true? (m/join-ready? done v [:root v])))
      (is (nil? (m/run done v r)))
      (is (nil? (get-in done [:env :native child-ticket])))
      (is (empty? (get-in done [:env :cleanup-cells])))
      (is (= (m/wr copied w) (m/wr done w))))))

(deftest cut-copy-clears-entry-on-parked-and-completed-generations
  (let [completed [:completed 1]
        before (reduce checked (entered-parked)
                       [{:t :t02 :w w :scope [:root w] :e :driver :value 0}
                        {:t :t04 :w w :e :completed :mode :callback
                         :filter {:mode :causal-follow :origin w}}
                        {:t :slice-enter :w w :r completed :th :completed-worker}
                        {:t :t05 :w w :r completed :kind :track :order 0 :debtor [:entity w :driver]}
                        {:t :t07 :w w :r completed :value :complete}
                        {:t :t38 :th :completed-worker}
                        {:t :t08 :w w :e :completed :debtor-world w :value :complete}
                        {:t :t20 :c :cut :scope [:root w]
                         :participants {:worlds #{w} :components #{} :systems #{}}}
                        {:t :t21 :c :cut}
                        {:t :t22 :c :cut}])
        source (m/wr before w)
        basis (get-in before [:cuts :cut :basis])
        action {:t :t23 :c :cut :v v :k [:cap 0]}
        after (checked before action)]
    (is (= #{r completed} (set (keys (:runs (m/wr after v))))))
    (doseq [run [r completed]]
      (is (true? (:cps-entered? (m/run before w run))))
      (is (true? (get-in basis [w :runs run :cps-entered?])))
      (is (not (contains? (m/run after v run) :cps-entered?)))
      (rejects-injected-entry before action after run))
    (is (= :inherited (:status (m/run after v r))))
    (is (= :completed (:status (m/run after v completed))))
    (is (= 1 (:finalization-sequence (m/run after v r))))
    (is (= (:runs source) (:runs (m/wr after w))))
    (is (= basis (get-in after [:cuts :cut :basis])))
    (is (= basis (get-in after [:worlds v :lineage :basis])))))
