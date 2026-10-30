(ns org.replikativ.spindel.lifetime.run12-check
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.lifetime.bfs-check :as b]
            [org.replikativ.spindel.lifetime.check-io :as io]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.run9-check :as r9]
            [org.replikativ.spindel.lifetime.run10-check :as r10]
            [org.replikativ.spindel.lifetime.run11-check :as r11]))

(def scope [:scope :id 0])
(def child [:spin 1])
(def cr [child 1])
(def sig [:signal 0])
(def enter {:t :slice-enter :th :host :w b/w :r b/r})
(def exit {:t :t38 :th :host})
(def cancel {:t :t11 :w b/w :r b/r})
(def simple [b/invoke enter cancel])
(def qcut
  {:t :t20q :c [:cut 0] :scope scope
   :participants {:worlds #{b/v} :components #{} :systems #{:memory}}})
(def merge-child (assoc b/seal :kind :merge))

(def dvergr
  [(assoc b/following :systems #{:memory})
   {:t :t12 :w b/v :scope scope :parent [:root b/v]}
   {:t :t04 :w b/v :scope scope :e b/e :mode :callback}
   {:t :t05 :w b/v :r b/r :kind :await-once :debtor [:entity b/v child]}
   {:t :t05 :w b/v :r cr :kind :external :debtor [:host :native]}
   {:t :t35 :th :host :op {:kind :resume :w b/v :o [:o 2]}}
   {:t :native-progress :n [:cancel [:o 2]] :state :joined}
   {:t :slice-enter :th :host :w b/v :r cr}
   {:t :t11 :w b/v :r b/r}])

(def joins (mapv #(hash-map :t :join :w b/v :x %) [b/r scope b/v]))

(def write-prefix
  [{:t :t02 :w b/w :e sig :value 0}
   (assoc b/invoke :e child)
   {:t :t05 :w b/w :r cr :kind :track :debtor [:entity b/w sig]}
   {:t :t07 :w b/w :r cr :value 0}
   b/invoke enter cancel])

(defn retained-source-prefix [kind]
  [{:t :t12 :w b/w :scope scope :parent b/root}
   {:t :t02 :w b/w :scope scope :e sig :kind kind :value 0}
   (assoc b/following :systems #{:memory})
   {:t :t04 :w b/v :e child}
   {:t :t05 :w b/v :r cr :kind (if (= kind :signal) :track :external)
    :debtor [:entity b/w sig]}
   b/invoke enter cancel
   {:t :t13 :w b/w :scope scope}])

(def cases
  {"dvergr" {:actions (into dvergr (concat joins [qcut merge-child exit] joins
                                           [(assoc qcut :c [:cut 1]) {:t :t25 :c [:cut 1]} merge-child]))}
   "timeout" {:actions (conj dvergr (assoc (first joins) :timeout? true))}
   "write-existing" {:actions (into write-prefix [{:t :signal-write :th :host :w b/w :e sig :value 1}
                                                  {:t :t08 :w b/w :e sig :value 1}])}
   "write-retained" {:actions (conj (retained-source-prefix :signal)
                                    {:t :signal-write :w b/w :th :host :e sig :value 1})}
   "write-absent" {:actions [b/invoke {:t :t02 :w b/w :r b/r :e sig} enter cancel
                             {:t :signal-write :th :host :w b/w :e sig :value 1}]}
   "write-released" {:actions (into simple [{:t :t34 :w b/w}
                                            {:t :signal-write :th :host :w b/w :e sig :value 1}])}
   "create-spin" {:actions (conj simple {:t :t01 :th :host :w b/w :e child})}
   "create-await" {:actions (conj simple {:t :t05 :th :host :w b/w :r b/r :kind :await-once
                                          :debtor [:entity b/w child]})}
   "create-signal" {:actions (conj simple {:t :t02 :th :host :w b/w :e sig})}
   "restart" {:actions (conj dvergr {:t :t04 :w b/v :scope scope :e child :mode :callback})}
   "l25-no-physical" {:actions simple :target :L25 :last-action {:corrupt :no-physical}}
   "l25-obligation" {:actions simple :target :L25 :last-action {:corrupt :obligation}}
   "tl5-complete" {:actions (conj simple {:t :t07 :th :host :w b/w :r b/r})
                   :target :TL5 :last-action {:corrupt :complete}}})

(def findings
  {"F58-completion-delivery" {:finding :F58 :target :L15
                              :actions [b/invoke enter {:t :t07 :w b/w :r b/r} {:t :queued :w b/w}]}
   "F58-supersede" {:finding :F58 :target :L15
                    :actions [b/invoke enter {:t :t09 :w b/w :e b/e}
                              {:t :t07 :w b/w :r [b/e 2]}]}
   "F59-child-scope" {:finding :F59 :target :L25
                      :actions [b/invoke {:t :t12 :w b/w :scope scope :parent b/r} enter cancel]}})

(defn checked [actions]
  (let [result (b/execute actions)]
    (is (empty? (b/violations result)) (pr-str (b/violations result)))
    result))

(defn corrupt [s kind]
  (case kind
    :no-physical (assoc-in s [:env :threads :host :run] nil)
    :obligation (assoc-in s [:worlds b/w :obligations [:o 99]]
                          {:kind :timer :creditor [:run b/w b/r] :debtor [:host :timer]
                           :standing? false :slot :armed})
    :complete (assoc-in s [:worlds b/w :entities b/e] (assoc (m/row :spin b/root) :completed? true))))

(deftest run12-artifacts
  (doseq [file (io/read-witness "run12/index.edn")]
    (testing file
      (let [{:keys [actions last-action target]} (io/read-witness file)
            finding (:finding (io/read-witness file))
            result (if finding (b/execute actions) (checked actions))]
        (is (seq actions))
        (is (= (case file
                 "run12/dvergr.edn" [::m/not-quiescent ::m/not-quiescent]
                 "run12/timeout.edn" [::m/join-timeout]
                 "run12/write-released.edn" [::m/released]
                 ("run12/create-spin.edn" "run12/create-await.edn" "run12/create-signal.edn") [::m/cancelled]
                 [])
               (mapv :error (keep :refusal (:trace result)))))
        (when finding
          (is (not-any? :refusal (:trace result)))
          (is (empty? (b/violations (b/execute (pop actions)))))
          (is (empty? (b/violations result)) (pr-str (b/violations result))))
        (when last-action
          (let [corruption (:corrupt last-action)
                edge (peek (:trace result))
                bad (corrupt (:state result) corruption)
                errors (if (= target :TL5) (inv/edge-check (assoc edge :after bad)) (inv/check bad))]
            (is (some #(= target (:id %)) errors) (pr-str errors))))))))

(deftest dvergr-physical-exit
  (let [result (checked dvergr) s (:state result)
        row (m/run s b/v cr)
        callback (filter #(= :host-delivery (:event %)) (:events s))]
    (is (not-any? :refusal (:trace result)))
    (is (= :unwinding (:status row)))
    (is (= [cr b/r scope [:root b/v] b/v] (:anchor row)))
    (is (nil? (m/ent s b/v child)))
    (is (= [::m/cancelled] (mapv :value callback)))
    (is (false? (m/quiescent? s b/v)))
    (doseq [join joins]
      (let [observed (m/attempt s join)
            timed (m/attempt s (assoc join :timeout? true))]
        (is (= {:complete? false :busy [cr]} (:observation observed)))
        (is (= s (:state observed) (:state timed)))
        (is (= ::m/join-timeout (get-in timed [:refusal :error])))
        (is (= [cr] (get-in timed [:refusal :busy])))))
    (is (= [[b/v cr]] (get-in (m/attempt s qcut) [:refusal :running])))
    (is (= ::m/not-quiescent (get-in (m/attempt s merge-child) [:refusal :error])))
    (let [after (:state (checked (conj dvergr exit)))]
      (is (nil? (m/run after b/v cr)))
      (is (m/quiescent? after b/v))
      (doseq [join joins] (is (true? (get-in (m/attempt after join) [:observation :complete?]))))
      (is (nil? (:refusal (m/attempt after qcut))))
      (is (nil? (:refusal (m/attempt after merge-child)))))))

(deftest unwinding-writes-and-refusals
  (let [s (:state (checked write-prefix))
        write {:t :signal-write :th :host :w b/w :e sig :value 1}
        after (:state (b/execute s [write]))
        rerun (:state (b/execute after [{:t :t08 :w b/w :e sig :value 1}]))]
    (is (= 1 (:result (m/ent after b/w sig))))
    (doseq [field [:runs :obligations]] (is (= (get (m/wr s b/w) field) (get (m/wr after b/w) field))))
    (is (= (set (keys (:entities (m/wr s b/w)))) (set (keys (:entities (m/wr after b/w))))))
    (is (= [child 2] (m/current rerun b/w child)))
    (is (= :running (:status (m/run rerun b/w [child 2])))))
  (doseq [kind [:signal :atom]]
    (let [actions [b/invoke {:t :t02 :w b/w :r b/r :kind kind :e sig} enter cancel]
          s (:state (checked actions))
          result (m/attempt s {:t :signal-write :th :host :w b/w :e sig :value 1})]
      (is (nil? (m/ent s b/w sig)))
      (is (nil? (:refusal result)))
      (is (= (m/non-idle-projection s) (m/non-idle-projection (:state result))))))
  (let [s (:state (checked simple))]
    (doseq [t [:t01 :t02 :t03 :t04 :t05 :t12 :t19 :t20 :t20q]]
      (let [result (m/attempt s {:t t :th :host :w b/w})]
        (is (= ::m/cancelled (get-in result [:refusal :error])))
        (is (= s (:state result)))))
    (is (= (m/non-idle-projection s)
           (m/non-idle-projection (:state (m/attempt s {:t :t07 :w b/w :r b/r :th :host})))))))

(deftest unwinding-writes-retained-ownerless-rows
  (doseq [kind [:signal :atom]]
    (let [prefix (retained-source-prefix kind)
          before (:state (checked prefix))
          result (checked (conj prefix {:t :signal-write :w b/w :th :host :e sig :value 1}))
          after (:state result)]
      (is (not-any? :refusal (:trace result)))
      (is (m/ent before b/w sig))
      (is (nil? (:owner (m/ent before b/w sig))))
      (is (= #{:dep} (m/reasons before b/w sig)))
      (is (= 1 (:result (m/ent after b/w sig))))
      (is (= (set (keys (:entities (m/wr before b/w))))
             (set (keys (:entities (m/wr after b/w)))))))))

(deftest native-and-slice-exit-order
  (let [prefix [b/invoke {:t :t05 :w b/w :r b/r :kind :external :debtor [:host :native]}
                {:t :t35 :th :host :op {:kind :resume :w b/w :o [:o 1]}} enter cancel]
        joined {:t :native-progress :n [:cancel [:o 1]] :state :joined}]
    (doseq [order [[exit joined] [joined exit]]]
      (let [result (checked (into prefix order))
            middle (:after (nth (:trace result) (count prefix)))
            after (:state result)]
        (is (= :unwinding (:status (m/run middle b/w b/r))))
        (is (nil? (m/run after b/w b/r)))
        (is (m/quiescent? after b/w)))))
  (let [result (checked [b/invoke {:t :t05 :w b/w :r b/r :kind :external :debtor [:host :native]} cancel])
        s (:state result)]
    (is (= :unwinding (:status (m/run s b/w b/r))))
    (is (= :cancel-requested (get-in s [:env :native [:cancel [:o 1]] :state])))
    (is (= [b/r] (m/join-blockers s b/w b/root)))))

(deftest released-world-join
  (let [released (:state (checked (conj simple {:t :t34 :w b/w})))
        join {:t :join :w b/w :x b/w}
        exited (:state (b/execute released [exit]))
        unbound (:state (b/execute exited [{:t :thread-entry :th :host
                                            :thread {:world nil :scope nil :run nil}}]))]
    (is (nil? (m/run released b/w b/r)))
    (is (false? (get-in (m/attempt released join) [:observation :complete?])))
    ;; Keeping a world selected without an active slice is not physical work.
    (is (true? (get-in (m/attempt exited join) [:observation :complete?])))
    (is (true? (get-in (m/attempt unbound join) [:observation :complete?])))
    (doseq [t [:t01 :t02 :t03 :t04 :t05 :t07 :t12 :t19 :t20 :signal-write :t06]]
      (is (= ::m/released (get-in (m/attempt released {:t t :th :host :w b/w}) [:refusal :error]))))))

(deftest restart-distinct-generations
  (let [s (:state (checked (:actions (cases "restart"))))]
    (is (= :unwinding (:status (m/run s b/v cr))))
    (is (= :running (:status (m/run s b/v [child 2]))))
    (is (= [child 2] (m/current s b/v child)))
    (is (= cr (get-in s [:env :threads :host :run])))
    (is (empty? (inv/l02 s)))))

(deftest unwinding-completion-is-an-exact-no-op
  (let [result (checked (conj simple {:t :t07 :th :host :w b/w :r b/r}))
        edge (peek (:trace result))
        corrupted (assoc-in (:after edge) [:env :threads :host :unexpected] true)]
    (is (= (dissoc (:before edge) :events) (dissoc (:after edge) :events)))
    (is (some #(= :TL5 (:id %)) (inv/edge-check (assoc edge :after corrupted))))))

(deftest join-monitor-negative-controls
  (let [s (:state (checked simple)) action {:t :join :w b/w :x b/r}
        edge {:before s :after s :action action :observation {:complete? true :busy []}}]
    (is (some #(= :TL19 (:id %)) (inv/edge-check edge)))
    (is (some #(= :TL19 (:id %))
              (inv/edge-check (assoc edge :action (assoc action :timeout? true)
                                     :observation nil :refusal {:error ::m/join-timeout :busy []}))))))

(deftest t21-and-t25-unwinding
  (let [fence (assoc qcut :t :t20)
        result (checked (into dvergr [fence {:t :t21 :c [:cut 0]}]))
        s (:state result)
        exited (:state (b/execute s [exit {:t :t21 :c [:cut 0]}]))]
    (is (= :fenced (get-in s [:cuts [:cut 0] :phase])))
    (is (= :ready (get-in exited [:cuts [:cut 0] :phase]))))
  (let [fence (assoc qcut :t :t20 :scope b/root :participants {:worlds #{b/w} :components #{} :systems #{}})
        prefix [b/invoke {:t :t05 :w b/w :r b/r :kind :external :debtor [:host :native]} cancel fence]
        s (:state (checked prefix))
        after (:state (checked (conj prefix {:t :t25 :c [:cut 0]})))]
    (is (= :unwinding (:status (m/run after b/w b/r))))
    (is (= (get-in s [:env :native]) (get-in after [:env :native])))
    (is (= :cancel-requested (get-in after [:env :native [:cancel [:o 1]] :state])))))

(deftest close-scope-anchor
  (let [result (checked (conj dvergr {:t :t13 :w b/v :scope scope}))
        s (:state result)
        joined (m/attempt s {:t :join :w b/v :x scope :timeout? true})]
    (is (nil? (get-in s [:worlds b/v :scopes scope])))
    (is (= [cr] (get-in joined [:refusal :busy])))
    (is (empty? (inv/l02 s)))
    (is (empty? (inv/l06 s)))
    (is (nil? (m/ent s b/v child)))))

(deftest idle-coexists-with-unwinding
  (let [actions [{:t :t02 :w b/w :e sig}
                 {:t :t01 :w b/w :e b/e :tok [:tok 0]}
                 (assoc b/invoke :tok [:tok 0])
                 {:t :t05 :w b/w :r b/r :kind :track :debtor [:entity b/w sig]}
                 {:t :t07 :w b/w :r b/r}
                 {:t :t09 :w b/w :e b/e :cause :rerun!}
                 (assoc enter :r [b/e 2]) (assoc cancel :r [b/e 2])]
        s (:state (checked actions))]
    (is (m/idle? s b/w b/e))
    (is (= :unwinding (:status (m/run s b/w [b/e 2]))))
    (is (empty? (inv/l07 s)))))

(deftest delivery-from-unwinding
  (let [prefix [(assoc b/invoke :e child)
                {:t :t05 :w b/w :r cr :kind :timer :debtor [:host :timer]}
                b/invoke enter cancel]
        s (:state (checked prefix))
        delivered (checked (conj prefix {:t :t06 :th :host :w b/w :o [:o 1] :value :delivered}))]
    (is (= :running (:status (m/run (:state delivered) b/w cr))))
    (is (some #(and (= :resume (:event %)) (= :delivered (:value %))) (:events (:state delivered))))
    (is (= (set (keys (:runs (m/wr s b/w)))) (set (keys (:runs (m/wr (:state delivered) b/w))))))
    (let [missing (m/attempt s {:t :t06 :th :host :w b/w :o [:o 99]})]
      (is (nil? (:refusal missing)))
      (is (= (m/non-idle-projection s) (m/non-idle-projection (:state missing)))))))

(deftest selected-world-write
  (let [actions [{:t :t02 :w b/w :e sig :value 0}
                 (assoc b/following :systems #{:memory})
                 {:t :t02 :w b/v :e sig :value 0}
                 {:t :t04 :w b/v :e b/e}
                 (assoc enter :w b/v) (assoc cancel :w b/v)
                 {:t :signal-write :w b/w :e sig :th :host :value 1}]
        s (:state (checked actions))]
    (is (= 0 (:result (m/ent s b/w sig))))
    (is (= 1 (:result (m/ent s b/v sig))))))

(deftest slice-budgets-and-observation-events
  (let [s (:state (checked [b/invoke enter]))]
    (is (= ::m/slice-busy (get-in (m/attempt s (assoc enter :th :foreign)) [:refusal :error])))
    (is (= ::m/thread-busy (get-in (m/attempt s {:t :thread-entry :th :host :thread {:world nil}}) [:refusal :error])))
    (let [exited (:state (b/execute s [exit]))]
      (is (not-any? #(= :slice-enter (:t %))
                    (m/enabled (assoc-in exited [:model :slices?] true))))))
  (let [result (checked [b/invoke {:t :t05 :w b/w :r b/r :kind :timer :debtor [:host :timer]}
                         {:t :t06 :w b/w :o [:o 1]} {:t :join :w b/w :x b/r}
                         {:t :join :w b/w :x b/root :timeout? true}])]
    (is (empty? (inv/check-trace (:trace result))))))

(def owned-child-bounds (assoc r11/owned-child-bounds :slices? true))
(defn owned-child-alphabet [s]
  (distinct
   (concat
    (r11/owned-child-alphabet s)
    (filter #(#{:slice-enter :t38 :join} (:t %)) (m/enabled s)))))

(deftest owned-child-exhaustion
  (let [report (b/bfs (m/init-state owned-child-bounds)
                      {:alphabet owned-child-alphabet :seconds 1800 :max-states 300000})]
    (b/report! :owned-child report)
    (is (= :exhausted (:status report)))
    (is (zero? (:pending report)))
    (is (zero? (:depth-cuts report)))
    (is (empty? (:findings report)) (pr-str (:findings report)))))

(defn -main [& [mode]]
  (require 'org.replikativ.spindel.lifetime.generative-check)
  (let [counts
        (binding [clojure.test/*report-counters* (ref clojure.test/*initial-report-counters*)]
          (doseq [[namespace excluded]
                  [['org.replikativ.spindel.lifetime.bfs-check (set b/search-checks)]
                   ['org.replikativ.spindel.lifetime.generative-check #{}]
                   ['org.replikativ.spindel.lifetime.run9-check #{'join-interleavings}]
                   ['org.replikativ.spindel.lifetime.run10-check #{'f57-release-interleavings}]
                   ['org.replikativ.spindel.lifetime.run11-check #{'owned-child-exhaustion}]
                   ['org.replikativ.spindel.lifetime.run12-check #{'owned-child-exhaustion}]]]
            (clojure.test/test-vars (remove #(excluded (:name (meta %))) (vals (ns-publics namespace)))))
          (println "LIFETIME UNIT-COUNTS" @clojure.test/*report-counters*)
          (when-not (= mode "regressions")
            (clojure.test/test-vars [#'owned-child-exhaustion #'r9/join-interleavings #'r10/f57-release-interleavings])
            (doseq [check b/search-checks]
              (clojure.test/test-vars [(ns-resolve 'org.replikativ.spindel.lifetime.bfs-check check)])))
          (let [counts @clojure.test/*report-counters*]
            (io/write-report! "counts.edn" (pr-str counts))
            (println "LIFETIME TOTAL-COUNTS" counts)
            counts))]
    (shutdown-agents)
    (System/exit (if (zero? (+ (:fail counts) (:error counts))) 0 1))))
