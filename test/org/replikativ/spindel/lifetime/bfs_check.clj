(ns org.replikativ.spindel.lifetime.bfs-check
  (:require [org.replikativ.spindel.lifetime.check-io :as check-io]
            [clojure.test :refer [deftest is testing]]
            [clojure.set :as set]
            [clojure.edn]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]))

(def w [:w 0]) (def v [:w 1]) (def e [:spin 0]) (def r [e 1])
(def root [:root w]) (def cap [:cap 0])
(def invoke {:t :t04 :w w :e e :mode :callback})
(def following {:t :t19 :w w :v v :k cap :scope root})
(def seal {:t :t26 :caller root :k cap :op :op :kind :merge})
(def prepare-op
  {:t :t27 :k cap :op :op :payload :p :bases {:a :base-a :b :base-b}
   :steps [{:id 0 :kind :system-merge :system :a :recovery :retry}
           {:id 1 :kind :stamp :system :b :recovery :query}]})
(defn execute
  ([actions] (execute (m/init-state) actions))
  ([initial actions]
   (reduce (fn [{:keys [state trace]} action]
             (let [{after :state refusal :refusal observation :observation} (m/attempt state action)]
               {:state after :trace (conj trace {:before state :action action :after after :refusal refusal :observation observation})}))
           {:state initial :trace []} actions)))
(defn violations [{:keys [trace state]}]
  (vec (concat (mapcat #(inv/check (:after %)) trace) (inv/check-trace trace))))
(defn cut-actions [mode]
  [{:t :t20 :c [:cut 0] :scope root :mode mode
    :participants {:worlds #{w} :components #{[w :sci-a] [w :sci-b]} :systems #{:a :b}}}
   {:t :t21 :c [:cut 0]} {:t :t22 :c [:cut 0]}
   {:t :t23 :c [:cut 0] :v [:w 2] :k [:cap 1] :mode mode}
   {:t :t24 :c [:cut 0] :e [:spin 3]}])

(defn configuration [mode]
  (execute
   (concat
    [following {:t :t02 :w w :e [:signal 0] :key :k}
     {:t :t02 :w w :e [:atom 0] :kind :atom}
     {:t :t01 :w w :e e :tok [:tok 0]} (assoc invoke :tok [:tok 0])
     {:t :t01 :w w :e e :tok [:tok 1]}
     {:t :t01 :w w :r r :e [:spin 1]} {:t :t01 :w w :r r :e [:spin 2]}
     {:t :t04 :w w :r r :e [:spin 1]} {:t :t04 :w w :r r :e [:spin 2]}
     {:t :t05 :w w :r r :kind :track :debtor [:entity w [:key w :k]]}]
    [{:t :t05 :w w :r r :kind :await-once :debtor [:entity w [:spin 1]]}
     {:t :t05 :w w :r [[:spin 1] 1] :kind :await-once :debtor [:entity w [:spin 2]]}
     {:t :t05 :w w :r [[:spin 2] 1] :kind :await-once :debtor [:entity w e]}]
    (cut-actions mode)
    [{:t :t04 :w w :e [:spin 3]}])))

(def local-por #{:t03 :t07 :t09 :t11 :t13 :t14 :t15 :t17 :t18 :signal-write})
(defn independent?
  "Conservative TL6 footprint certificate. Distinct acting worlds, no cut,
  fork ownership, cross-world endpoint, fdep or shared handle. Only local actions
  without fresh obligation ids qualify. Thus each reads/writes its own world and
  disjoint host rows; neither disables the other and both orders agree including
  monitor events. Cross-world deliveries/cuts/settlement always stay dependent."
  [s a b]
  (let [wa (:w a) wb (:w b)
        isolated? (fn [w]
                    (and (empty? (:fdeps (m/wr s w)))
                         (empty? (:releasing (m/wr s w)))
                         (not-any? #(= :fork (:kind %)) (vals (:entities (m/wr s w))))
                         (not-any? #(and (m/active-cuts (:phase %))
                                         (or (= w (:child %)) (contains? (get-in % [:participants :worlds]) w)))
                                   (vals (:cuts s)))
                         (not-any? (fn [[v _ ob]]
                                     (let [[kind dw _] (:debtor ob)]
                                       (and (= :entity kind) (not= v dw) (or (= dw w) (= v w))))) (inv/obligations s))))
        tokens (fn [w] (set (for [[tok h] (get-in s [:env :handles])
                                  :when (contains? (:touched h) w)] tok)))]
    (boolean (and wa wb (not= wa wb) (local-por (:t a)) (local-por (:t b))
                  (isolated? wa) (isolated? wb)
                  (empty? (set/intersection (tokens wa) (tokens wb)))))))

(defn advance-monitor [monitor events]
  (reduce (fn [{:keys [seen errors] :as mon} ev]
            (let [key (cond (= :resume (:event ev)) [:slot (:world ev) (:r ev) (:o ev)]
                            (and (= :host-delivery (:event ev)) (:causal? ev)) [:host (:world ev) (:o ev)])]
              (if-not key mon
                      {:seen (conj seen key) :errors (cond-> errors (seen key) (conj {:id :TL1 :evidence key}))})))
          {:seen monitor :errors []} events))

(defn compact-state-key
  "Lossless compressed structural EDN. Equality compares the complete bytes,
  never a digest. Structural tags give deterministic map/set order and types."
  [canonical-state]
  (let [out (java.io.ByteArrayOutputStream.)
        data (.getBytes (binding [*print-length* nil *print-level* nil
                                  *print-readably* true *print-meta* false *print-dup* false]
                          (pr-str (m/structural-key canonical-state))) "UTF-8")]
    (with-open [zip (java.util.zip.DeflaterOutputStream. out)]
      (.write zip data))
    (String. (.toByteArray out) "ISO-8859-1")))

(defn bfs
  "BFS with sleep sets; visited identity includes the sleep set and TL1 monitor.
  Exhausted means EVERY queued node was expanded, with no depth/state/time cut.
  Invalid successors are recorded and still expanded (no invariant pruning).
  Depth-cut successors never become fake terminal states. Hash equality uses full
  canonical values, not collision-prone integer hashes. Witnesses are BFS shortest
  in this alphabet (sleep reduction may select a commuting representative)."
  ([initial] (bfs initial {}))
  ([initial {:keys [max-states max-depth seconds alphabet por? max-heap-ratio compact-keys?]
             :or {max-states 10000 max-depth 40 seconds 40 alphabet m/enabled por? true max-heap-ratio 0.70}}]
   (let [started (System/nanoTime)
         initial-node {:state initial :actions [] :monitor #{} :sleep #{}}
         state-key (fn [s monitor sleep]
                     (let [canonical (m/canonical (assoc s :resume-monitor monitor :sleep sleep))]
                       (if compact-keys? (compact-state-key canonical) canonical)))
         initial-key (state-key initial #{} #{})]
     (loop [queue (conj clojure.lang.PersistentQueue/EMPTY initial-node)
            seen #{initial-key} counts {:states 1 :edges 0 :depth 0 :maximal 0 :slept 0 :candidates 0 :depth-cuts 0}
            findings {} covered #{}]
       (let [elapsed (/ (- (System/nanoTime) started) 1e9)
             runtime (Runtime/getRuntime)
             used-before (- (.totalMemory runtime) (.freeMemory runtime))
             collected? (> used-before (* 0.85 (.maxMemory runtime)))
             _ (when collected? (System/gc))
             heap-used (- (.totalMemory runtime) (.freeMemory runtime))
             stop (cond (and collected? (>= heap-used (* max-heap-ratio (.maxMemory runtime)))) :heap-limit
                        (>= elapsed seconds) :time-limit
                        (>= (count seen) max-states) :state-limit
                        (empty? queue) (if (pos? (:depth-cuts counts)) :depth-limit :exhausted))]
         (if stop
           (assoc counts :status stop :seconds elapsed :findings findings :transitions covered
                  :pending (count queue) :heap-used heap-used :heap-max (.maxMemory runtime)
                  :bounds (:model initial) :limits {:states max-states :depth max-depth :seconds seconds
                                                    :retained-heap-ratio max-heap-ratio :compact-keys? (boolean compact-keys?)}
                  :por-ratio (if (zero? (:candidates counts)) 0.0
                                 (double (/ (:slept counts) (:candidates counts)))))
           (let [{:keys [state actions monitor sleep]} (peek queue) queue (pop queue)
                 all (vec (m/structural-order (alphabet state))) depth (count actions)
                 counts (-> counts (update :candidates + (count all))
                            (update :maximal + (if (empty? all) 1 0)))
                 cutoff? (and (>= depth max-depth) (seq all))
                 result
                 (reduce
                  (fn [{:keys [queue seen counts findings covered prior] :as acc} action]
                    (if (and por? (sleep action))
                      (-> acc (update-in [:counts :slept] inc) (update :prior conj action))
                      (let [{after :state refusal :refusal observation :observation} (m/attempt state action)
                            edge {:before state :action action :after after :refusal refusal :observation observation}
                            mon (advance-monitor monitor (if (or refusal observation) [] (:events after)))
                            bad (concat (inv/check after) (inv/edge-check edge) (:errors mon))
                            next-actions (conj actions action)
                            sleep2 (if por? (set (filter #(independent? state action %) (into sleep prior))) #{})
                            stutter? (and (= (dissoc state :events) (dissoc after :events))
                                          (= monitor (:seen mon)) (= sleep sleep2))
                            key (when-not stutter? (state-key after (:seen mon) sleep2))
                            new? (and (not stutter?) (not (contains? seen key)))]
                        {:queue (if new? (conj queue {:state after :actions next-actions :monitor (:seen mon) :sleep sleep2}) queue)
                         :seen (if new? (conj seen key) seen)
                         :counts (cond-> (-> counts (update :edges inc) (update :depth max (inc depth)))
                                   new? (update :states inc))
                         :covered (if refusal covered (conj covered (:t action)))
                         :prior (conj prior action)
                         :findings (reduce (fn [fs violation]
                                             (if (contains? fs (:id violation)) fs
                                                 (assoc fs (:id violation) {:actions next-actions :violation violation}))) findings bad)})))
                  {:queue queue :seen seen :counts (cond-> counts cutoff? (update :depth-cuts inc))
                   :findings findings :covered covered :prior #{}}
                  (if cutoff? [] all))]
             (recur (:queue result) (:seen result) (:counts result) (:findings result) (:covered result)))))))))

(defn report! [name report]
  (println "LIFETIME BFS" name (pr-str (dissoc report :findings)))
  (println "LIFETIME FINDINGS" name (pr-str (:findings report)))
  (check-io/write-report! (str (clojure.core/name name) ".edn") (pr-str report)))

(deftest revised-regressions
  (doseq [[name actions]
          {:F01 [{:t :t02 :w w :e [:signal 0]} invoke
                 {:t :t05 :w w :r r :kind :track :debtor [:entity w [:signal 0]]}
                 {:t :t07 :w w :r r} {:t :t09 :w w :e e :cause :track :order 0}]
           :F02 [following seal]
           :F03 [invoke {:t :t05 :w w :r r :kind :timer :debtor [:host :executor]} following]
           :F04 [invoke {:t :t14 :w w :e e :pin? true} {:t :t14 :w w :e e :pin? false}]
           :F05 [following {:t :t31} {:t :t31 :phase :restart}]
           :F06 [following seal prepare-op {:t :t28 :op :op :i 0 :outcome :fail}
                 {:t :t30 :op :op :k cap :caller root :payload :p} {:t :t28 :op :op :i 0 :outcome :ok}]
           :F11 [invoke {:t :t09 :w w :e e} {:t :t11 :w w :r [e 2]}]
           :F16 [invoke {:t :t07 :w w :r r} {:t :t11 :w w :r r}]
           :F20 [invoke {:t :t02 :w w :e [:signal 0]}
                 {:t :t05 :w w :r r :kind :track :debtor [:entity w [:signal 0]]}
                 {:t :t06 :w w :o [:o 1]} {:t :t05 :w w :r r :kind :external :debtor [:host :native]}
                 {:t :t06 :w w :o [:o 1]}]}]
    (testing (str name) (is (empty? (violations (execute actions))) (pr-str (violations (execute actions)))))))

(deftest durable-and-memory-restart
  (doseq [systems [#{:a :b} #{:memory}]]
    (let [s (:state (execute [(assoc following :systems systems) {:t :t31} {:t :t31 :phase :restart}]))]
      (is (empty? (inv/check s)))
      (is (= (if (= systems #{:memory}) 0 1) (count (m/all-caps s))))
      (is (every? #(= :discard (:kind %)) (vals (m/all-records s)))))))

(deftest copy-provenance-and-dormancy
  (doseq [mode [:frozen :materialized]]
    (let [fixture (configuration mode)
          copied (dissoc (:entities (m/wr (:state fixture) [:w 2])) [:spin 3])]
      (is (= 3 (count (:worlds (:state fixture)))))
      (is (not-any? :refusal (:trace fixture)) (pr-str (keep :refusal (:trace fixture))))
      (is (empty? (violations fixture)) (pr-str (violations fixture)))
      (is (every? #(= :inherited (:origin %)) (vals copied)))
      (is (every? :source-world (vals copied))))))

(deftest refusal-and-canonical-contract
  (is (empty? (inv/check (m/init-state))))
  (is (= 46 (count m/transitions)))
  (let [s (:state (execute [following {:t :t04 :w v :e e}])) a (m/attempt s seal)]
    (is (= ::m/not-quiescent (get-in a [:refusal :error]))) (is (= s (:state a))))
  (let [s (m/init-state)] (is (= s (:state (m/attempt s {:t :t35 :th :foreign})))))
  (is (= (m/canonical (m/init-state)) (m/canonical (m/canonical (m/init-state))))))

(deftest broad-searches
  (doseq [[name initial]
          [[:root (m/init-state)]
           [:frozen (:state (configuration :frozen))]
           [:materialized (:state (configuration :materialized))]
           [:chain (:state (execute [following {:t :t19 :w v :v [:w 2] :k [:cap 1] :scope [:root v]}]))]]]
    (let [report (bfs initial {:seconds 3 :max-states 2000})]
      (report! name report)
      (is (empty? (:findings report)) (pr-str (:findings report))))))

(deftest reduced-complete-search
  (doseq [[name cfg] [[:one-spin {:spins 1 :signals 0 :atoms 0 :slices? true}]
                      [:source-only {:spins 0 :signals 1 :atoms 1}]]]
    (let [initial (m/init-state (merge {:worlds 1 :generations 1 :scopes 0 :handles 0 :cuts 0 :filters [:local] :invoke-modes [:callback]} cfg))
          report (bfs initial {:seconds 5400 :max-states 300000 :compact-keys? (= name :one-spin)})]
      (report! name report)
      (is (= :exhausted (:status report)))
      (is (empty? (:findings report)) (pr-str (:findings report))))))

(deftest shared-component-cuts
  (let [initial (update-in (:state (execute [following])) [:env :threads] dissoc :host)
        cuts [{:t :t20 :c [:cut 0] :scope root :coordinator :ca
               :participants {:worlds #{w} :components #{[w :a] [v :b]} :systems #{:a}}}
              {:t :t20 :c [:cut 1] :scope [:root v] :coordinator :cb
               :participants {:worlds #{v} :components #{[w :a] [v :b]} :systems #{:b}}}]
        alphabet (fn [s] (concat (for [cut cuts t [:t20 :t20q] :when (not (get-in s [:cuts (:c cut)]))]
                                   (assoc cut :t t))
                                 (for [[c cut] (:cuts s) t (case (:phase cut)
                                                             :fenced [:t21 :t25]
                                                             :ready [:t22 :t25]
                                                             :captured [:t25] [])] {:t t :c c})))
        report (bfs initial {:alphabet alphabet :seconds 30})]
    (report! :shared-cuts report)
    (is (= :exhausted (:status report))) (is (empty? (:findings report)) (pr-str (:findings report)))))

(deftest settlement-search
  (doseq [systems [#{:a :b} #{:memory :ram}]]
    (let [initial (:state (execute [(assoc following :systems systems)]))
          alphabet #(filter (fn [a] (#{:t26 :t27 :t28 :t29 :t30 :t31 :t32 :t33} (:t a))) (m/enabled %))
          report (bfs initial {:alphabet alphabet :seconds 900 :max-states 50000})]
      (report! (if (= systems #{:a :b}) :settlement-durable :settlement-memory) report)
      (is (= :exhausted (:status report)))
      (is (empty? (:findings report)) (pr-str (:findings report))))))

(deftest reduction-equivalence
  (let [setup [following {:t :t19 :w w :v [:w 2] :k [:cap 1] :scope root}
               {:t :t04 :w v :e e} {:t :t04 :w [:w 2] :e e}]
        initial (:state (execute setup))
        alphabet (fn [s] (for [w [v [:w 2]] :when (m/run s w r)] {:t :t11 :w w :r r}))
        full (bfs initial {:alphabet alphabet :por? false})
        reduced (bfs initial {:alphabet alphabet})
        a {:t :t11 :w v :r r} b {:t :t11 :w [:w 2] :r r}]
    (is (independent? initial a b))
    (is (= (m/canonical (:state (execute initial [a b])))
           (m/canonical (:state (execute initial [b a])))))
    (is (= :exhausted (:status full) (:status reduced)))
    (is (= (:findings full) (:findings reduced)))
    (is (pos? (:slept reduced)))
    (report! :por-check reduced)))

(deftest compact-key-contract
  (doseq [s (cons (m/init-state) (map :after (:trace (configuration :frozen))))]
    (let [canonical (m/canonical s)
          encoded (compact-state-key canonical)
          decoded (with-open [zip (java.util.zip.InflaterInputStream.
                                   (java.io.ByteArrayInputStream. (.getBytes encoded "ISO-8859-1")))]
                    (clojure.edn/read-string (slurp zip :encoding "UTF-8")))]
      (is (= (m/structural-key canonical) decoded))
      (is (= encoded (compact-state-key (m/canonical canonical))))
      (is (= encoded (binding [*print-length* 1 *print-level* 1 *print-readably* false]
                       (compact-state-key canonical))))))
  (let [initial (m/init-state {:worlds 1 :generations 1 :scopes 0 :handles 0 :cuts 0
                               :spins 0 :signals 1 :atoms 1 :filters [:local] :invoke-modes [:callback]})
        ordinary (bfs initial {:seconds 30})
        compact (bfs initial {:seconds 30 :compact-keys? true})
        fields [:status :states :edges :depth :depth-cuts :pending :findings :transitions]]
    (is (= :exhausted (:status ordinary) (:status compact)))
    (is (= (select-keys ordinary fields) (select-keys compact fields)))))

(deftest canonical-renaming
  (let [s (:state (execute [following invoke {:t :t05 :w w :r r :kind :timer :debtor [:host :executor]}]))
        renamed (clojure.walk/postwalk-replace {w [:w 80] v [:w 90] [:o 0] [:o 72] [:o 1] [:o 87]} s)]
    (is (= (m/canonical s) (m/canonical renamed)))
    (is (= (m/canonical s) (m/canonical (m/canonical s))))))

(deftest structural-canonical-contract
  (let [values [nil false true 0 1 1.0 1M 1/2 \a :a :ns/a 'a 'ns/a "a"
                [] [0] {} {0 :a} #{} #{0} [[:spin 1] 2]]
        reverse-maps (fn [s]
                       (clojure.walk/postwalk
                        #(if (map? %) (into (array-map) (reverse (vec %))) %) s))
        states (map :after (:trace (configuration :frozen)))]
    (is (= (count values) (count (set (map m/structural-key values)))))
    (is (= (m/structural-order values) (m/structural-order (reverse values))))
    (doseq [s states]
      (is (= (m/canonical s) (m/canonical (reverse-maps s))))
      (is (= (m/canonical s) (m/canonical (m/canonical s))))
      (is (not= (m/canonical s) (m/canonical (assoc-in s [:model :depth] 999)))))
    (is (not= (m/canonical (m/init-state))
              (m/canonical (assoc (m/init-state) :sleep #{invoke}))))))

(defn cross-world-copy []
  (execute [{:t :t12 :w w :scope [:scope 0] :parent root}
            {:t :t02 :w w :scope [:scope 0] :e [:signal 0]}
            following {:t :t04 :w v :e e}
            {:t :t05 :w v :r r :kind :track :debtor [:entity w [:signal 0]]}
            {:t :t05 :w v :r r :kind :timer :debtor [:host :executor]}
            {:t :t20 :c [:cut 0] :scope [:root v]
             :participants {:worlds #{v} :components #{[v :sci-a]} :systems #{:a}}}
            {:t :t21 :c [:cut 0]} {:t :t22 :c [:cut 0]}
            {:t :t23 :c [:cut 0] :v [:w 2] :k [:cap 1] :mode :frozen}]))

(deftest resolved-copy-and-cut-regressions
  (let [base (cross-world-copy) child [:w 2] s (:state base)
        timer (first (for [[o ob] (:obligations (m/wr s child)) :when (= :timer (:kind ob))] o))]
    (is (empty? (violations base)) (pr-str (violations base)))
    (is (not-any? #(= child (:join-bundle %)) (:queue (m/wr s w))))
    (let [admitted (execute s [{:t :t24 :c [:cut 0]} {:t :t36 :w w}])]
      (is (empty? (violations admitted)))
      (is (some #(= [:bundle child #{[:signal 0]}] %) (:fdeps (m/wr (:state admitted) w)))))
    (is (:refusal (m/attempt s {:t :t06 :w child :o timer})))
    (let [s (:state (execute s [{:t :t24 :c [:cut 0]} {:t :t15 :w child}
                                {:t :t26 :caller [:root v] :k [:cap 1] :op :seal :kind :discard}]))]
      (is (:refusal (m/attempt s {:t :t06 :w child :o timer}))))
    (let [failed (execute s [{:t :t25 :c [:cut 0]}])]
      (is (empty? (violations failed)) (pr-str (violations failed)))
      (is (nil? (m/cap (:state failed) [:cap 1])))
      (is (nil? (m/ent (:state failed) v [:fork child])))))
  (let [base (execute [(assoc invoke :mode :deref :filter {:mode :causal-follow :origin w})
                       {:t :t04 :w w :e [:spin 1]}
                       {:t :t05 :w w :r r :kind :await-once :debtor [:entity w [:spin 1]]}
                       {:t :t05 :w w :r [[:spin 1] 1] :kind :await-once :debtor [:entity w e]}])
        copied (execute (:state base) (butlast (cut-actions :frozen)))
        host (get-in copied [:state :worlds [:w 2] :obligations [:o 0]])]
    (is (:descriptor? host)) (is (nil? (:cont host)))
    (let [delivered (execute (:state copied)
                             [{:t :t24 :c [:cut 0]} {:t :t06 :w [:w 2] :o [:o 2]}
                              {:t :t07 :w [:w 2] :r r} {:t :t08 :w [:w 2] :e e}
                              {:t :t08 :w [:w 2] :e e}])]
      (is (empty? (violations delivered)) (pr-str (violations delivered)))
      (is (= 1 (count (for [edge (:trace delivered) ev (:events (:after edge))
                            :when (and (= :host-delivery (:event ev)) (:causal? ev))] ev)))))))

(deftest two-step-recovery-and-authority
  (let [result (execute [following seal prepare-op
                         {:t :t28 :op :op :i 0 :outcome :unknown :committed? true}
                         {:t :t31} {:t :t31 :phase :restart}
                         {:t :t30 :op :op :k cap :caller root :payload :p}
                         {:t :t28 :op :op :i 0 :outcome :ok}
                         {:t :t28 :op :op :i 1 :outcome :ok} {:t :t29 :op :op}])]
    (is (empty? (violations result)) (pr-str (violations result)))
    (is (= :merged (:disposition (m/cap (:state result) cap))))
    (is (= #{[:op 0] [:op 1]} (:adapter-effects (:state result)))))
  (let [s (:state (execute [following seal prepare-op]))]
    (doseq [a [{:t :t30 :op :op :k cap :caller :intruder :payload :p}
               {:t :t30 :op :op :k cap :caller root :payload :changed}]]
      (is (:refusal (m/attempt s a)))
      (is (= s (:state (m/attempt s a)))))))

(def new-witnesses
  {:inherited-creations [invoke {:t :t01 :w w :r r :e [:spin 1]}
                         {:t :t01 :w w :r r :e [:spin 2]}
                         {:t :t05 :w w :r r :kind :await-once :debtor [:entity w [:spin 2]]}
                         following {:t :t11 :w w :r r}]
   :host-readthrough [invoke following {:t :t04 :w v :e e :mode :callback}]
   :dirty-cache [{:t :t01 :w w :e e :tok [:tok 0]} (assoc invoke :tok [:tok 0])
                 {:t :t07 :w w :r r} {:t :t11 :w w :r r} (assoc invoke :tok [:tok 0])]
   :dormant-timer (into [invoke {:t :t05 :w w :r r :kind :timer :debtor [:host :executor]}]
                        (butlast (cut-actions :frozen)))
   :control-queue [following {:t :t13 :w w :scope root}]
   :aggregate-census
   [{:t :t12 :w w :scope [:scope 0] :parent root}
    {:t :t02 :w w :scope [:scope 0] :e [:signal 0]}
    {:t :t04 :w w :scope [:scope 0] :e [:spin 1] :mode :callback}
    following {:t :t04 :w v :e e}
    {:t :t05 :w v :r r :kind :track :debtor [:entity w [:signal 0]]}
    {:t :t05 :w v :r r :kind :await-once :debtor [:entity w [:spin 1]]}
    {:t :t19 :w v :v [:w 2] :k [:cap 1] :scope [:root v]}
    {:t :t11 :w v :r r} {:t :t13 :w w :scope [:scope 0]}]
   :foreign-reclaim
   [{:t :t12 :w w :scope [:scope 0] :parent root}
    {:t :t02 :w w :scope [:scope 0] :e [:signal 0]}
    following {:t :t04 :w v :e e}
    {:t :t05 :w v :r r :kind :track :debtor [:entity w [:signal 0]]}
    {:t :t13 :w w :scope [:scope 0]} {:t :unsubscribe :w v :o [:o 1]}]
   :foreign-release
   [following {:t :t02 :w w :e [:signal 0]} {:t :t04 :w v :e e}
    {:t :t05 :w v :r r :kind :track :debtor [:entity w [:signal 0]]}
    {:t :t34 :w w}]
   :mixed-partition
   [(assoc following :systems #{:a :memory})
    {:t :t33 :k cap :op :split :successors [{:k [:cap 1] :scope #{:a}} {:k [:cap 2] :scope #{:memory}}]}
    {:t :t31} {:t :t31 :phase :restart}]})

(defn first-failure
  "Require a legal trace and a fully valid prefix, not a downstream symptom."
  [actions]
  (loop [state (m/init-state) actions actions monitor #{}]
    (when-let [a (first actions)]
      (let [{after :state refusal :refusal observation :observation} (m/attempt state a)
            edge {:before state :action a :after after :refusal refusal :observation observation}
            mon (advance-monitor monitor (if (or refusal observation) [] (:events after)))
            bad (vec (concat (inv/check after) (inv/edge-check edge) (:errors mon)))]
        (cond refusal nil
              (seq bad) (when (empty? (rest actions)) bad)
              :else (recur after (rest actions) (:seen mon)))))))

(defn shortest-subsequence [actions target]
  (or (first (for [mask (sort-by #(Long/bitCount %) (range 1 (bit-shift-left 1 (count actions))))
                   :let [candidate (vec (keep-indexed #(when (bit-test mask %1) %2) actions))]
                   :when (some #(= target (:id %)) (first-failure candidate))] candidate)) actions))

(deftest normative-new-witnesses
  (doseq [[name actions] new-witnesses]
    (let [result (execute actions) bad (violations result)]
      (check-io/write-report! (str "witness-" (clojure.core/name name) ".edn")
                              (pr-str {:actions actions :violations bad :valid-prefix? (boolean (first-failure actions))}))
      (is (seq actions) (str "regression " name))
      (println "LIFETIME NEW" name (pr-str {:actions actions :violations bad
                                            :refusals (vec (keep :refusal (:trace result)))}))
      (is (not-any? :refusal (:trace result)))
      (is (empty? bad) (str name " " (pr-str bad))))))

(deftest smaller-settlement-exhaustion
  (let [initial (:state (execute (m/init-state {:steps 1}) [(assoc following :systems #{:a})]))
        alphabet #(filter (fn [a] (#{:t26 :t27 :t28 :t29 :t30 :t31 :t32 :t33} (:t a))) (m/enabled %))
        report (bfs initial {:alphabet alphabet :seconds 900 :max-states 30000})]
    (report! :settlement-one-step report)
    (is (= :exhausted (:status report)))
    (is (empty? (:findings report)) (pr-str (:findings report)))))

(deftest transition-coverage
  (let [traces [[invoke {:t :t01 :w w :r r :e [:spin 1]}
                 {:t :t03 :w w :r r :key :site} {:t :t02 :w w :e [:signal 0]}
                 {:t :t05 :w w :r r :kind :timer :debtor [:host :executor]}
                 {:t :t06 :w w :o [:o 1]} {:t :t09 :w w :e e}
                 {:t :t10 :w w :r r} {:t :t11 :w w :r [e 2]}]
                [{:t :t12 :w w :scope [:scope 0] :parent root} {:t :t13 :w w :scope [:scope 0]}
                 invoke {:t :t14 :w w :e e :pin? true} {:t :t14 :w w :e e :pin? false} {:t :t15 :w w}
                 {:t :t34 :w w}]
                [{:t :t01 :w w :e e :tok [:tok 0]} (assoc invoke :tok [:tok 0])
                 {:t :t07 :w w :r r} {:t :t08 :w w :e e}
                 {:t :t16 :tok [:tok 0]} {:t :t17 :w w :e e :tok [:tok 0]} {:t :t18 :w w}]
                (cut-actions :frozen)
                (into [(assoc (first (cut-actions :frozen)) :t :t20q)]
                      (drop 2 (cut-actions :frozen)))
                (conj (vec (butlast (cut-actions :frozen))) {:t :t25 :c [:cut 0]})
                [following seal prepare-op {:t :t28 :op :op :i 0 :outcome :fail}
                 {:t :t30 :op :op :k cap :caller root :payload :p}
                 {:t :t28 :op :op :i 0 :outcome :ok} {:t :t28 :op :op :i 1 :outcome :ok}
                 {:t :t29 :op :op} {:t :t31} {:t :t31 :phase :restart}]
                [following {:t :t32 :k cap :successor [:cap 1] :holder :h :op :transfer}]
                [following {:t :t33 :k cap :op :partition :successors [{:k [:cap 1] :scope #{:a}} {:k [:cap 2] :scope #{:b}}]}]
                [following seal (assoc prepare-op :steps []) {:t :t29 :op :op} {:t :t36 :w w}]
                [following {:t :t04 :w v :e e}
                 {:t :t05 :w v :r r :kind :await-once :debtor [:entity w [:spin 1]]}
                 {:t :t37 :w w}]
                [{:t :t35 :th :host}]
                [invoke {:t :slice-enter :th :host :w w :r r} {:t :t38 :th :host}]]
        cleanup-actions [invoke {:t :slice-enter :th :host :w w :r r}
                         {:t :t02 :w w :scope r :e :cleanup-cell :kind :atom :value 1}
                         {:t :t11 :w w :r r}
                         {:t :cleanup-adopt :n [:cps-exit w r] :th :host}
                         {:t :cleanup-cell :th :host :cell [w r :cleanup-cell] :value 2}
                         {:t :cleanup-park :th :host} {:t :t38 :th :host}
                         {:t :cleanup-deliver :n [:cps-exit w r] :sequence 1 :value :done}
                         {:t :cleanup-claim :n [:cps-exit w r] :th :host}
                         {:t :cleanup-return :th :host} {:t :t38 :th :host}]
        results (conj (mapv execute traces)
                      (execute (m/init-state {:cps-exit? true :slices? true}) cleanup-actions))
        covered (set (for [result results edge (:trace result) :when (not (:refusal edge))] (get-in edge [:action :t])))]
    (println "LIFETIME TRANSITION-COVERAGE" (pr-str covered))
    (is (= (set (keys m/transitions)) covered))
    (doseq [result results]
      (is (not-any? :refusal (:trace result)) (pr-str (keep :refusal (:trace result))))
      (is (empty? (violations result)) (pr-str (violations result))))))

(deftest settlement-pareto-fallbacks
  (doseq [[name steps split?] [[:partitioned-one-step 1 true] [:linear-two-step 2 false]]]
    (let [initial (:state (execute (m/init-state {:steps steps}) [following]))
          alphabet #(filter (fn [a] (and (#{:t26 :t27 :t28 :t29 :t30 :t31 :t32 :t33} (:t a))
                                         (or split? (not (#{:t32 :t33} (:t a)))))) (m/enabled %))
          report (bfs initial {:alphabet alphabet :seconds 900 :max-states 50000})]
      (report! name report)
      (is (= :exhausted (:status report)))
      (is (empty? (:findings report)) (pr-str (:findings report))))))

(deftest nested-reentry-bound
  (let [setup [invoke {:t :t04 :w w :e [:spin 1]}
               {:t :t05 :w w :r r :kind :await-reactive :debtor [:entity w [:spin 1]]}
               {:t :t06 :w w :o [:o 2]} {:t :t09 :w w :e e}
               {:t :t05 :w w :r [e 2] :kind :await-reactive :debtor [:entity w [:spin 1]]}
               {:t :t06 :w w :o [:o 3]} {:t :t07 :w w :r [[:spin 1] 1]}]
        s (:state (execute setup)) action {:t :queued :w w}]
    (is (m/within-bounds? s))
    (is (not (m/within-bounds? (m/step s action))))
    (is (not (some #{action} (m/enabled s))))))

(deftest gc-idle-queue-projection
  (let [actions [{:t :t01 :w w :e e :tok [:tok 0]} (assoc invoke :tok [:tok 0])
                 {:t :t07 :w w :r r} {:t :t11 :w w :r r}
                 {:t :t16 :tok [:tok 0]} {:t :t17 :w w :e e :tok [:tok 0]}]
        result (execute actions)]
    (is (empty? (violations result)) (pr-str (violations result)))))

(def run3-witnesses
  {:releasing-census (get new-witnesses :foreign-reclaim)
   :crash-before-restart (vec (butlast (get new-witnesses :mixed-partition)))
   :cut-release-isolation (vec (cut-actions :frozen))
   :cut-rollback-isolation (conj (vec (butlast (cut-actions :frozen))) {:t :t25 :c [:cut 0]})
   :foreign-await-start [following {:t :t04 :w v :e e}
                         {:t :t05 :w v :r r :kind :await-once :debtor [:entity w [:spin 1]]}]
   :settle-owner [following seal {:t :t13 :w w :scope root}]
   :fork-release-gap [following seal (assoc prepare-op :steps []) {:t :t29 :op :op}]
   :ack-preempted (conj (vec (get new-witnesses :foreign-release)) {:t :queued :w v})})

(deftest run3-minimal-counterexamples
  (doseq [[name actions] run3-witnesses]
    (let [result (execute actions)]
      (check-io/write-report! (str "minimal-" (clojure.core/name name) ".edn")
                              (pr-str {:actions actions :valid-prefix? (boolean (first-failure actions))
                                       :violations (violations result)}))
      (is (not-any? :refusal (:trace result)))
      (is (empty? (violations result)) (str name " " (pr-str (violations result)))))))

(deftest finite-site-budgets
  (let [initial (m/init-state {:worlds 1 :world-ids 1 :spins 1 :signals 0 :atoms 0 :cuts 0 :handles 0})
        s (:state (execute initial [invoke invoke]))]
    (is (= 2 (count (:obligations (m/wr s w)))))
    (is (not-any? #(= :t04 (:t %)) (m/enabled s)))
    (is (m/within-bounds? s))
    (is (not (m/within-bounds? (m/step s invoke)))))
  (let [s (:state (execute [following {:t :t19 :w v :v [:w 2] :k [:cap 1] :scope [:root v]}]))
        a {:t :t19 :w [:w 2] :v [:w 3] :k [:cap 2] :scope [:root [:w 2]]}]
    (is (not (m/within-bounds? (m/step s a))))
    (is (not (some #{a} (m/enabled s))))))

(deftest mixed-partition-after-restart
  (let [result (execute (get new-witnesses :mixed-partition))
        s (:state result) vanished (get (m/vanished-caps s) [:cap 2])]
    (is (empty? (inv/check s)) (pr-str (inv/check s)))
    (is (= :discarded (:disposition vanished)))
    (is (nil? (m/cap s [:cap 2])))
    (is (false? (:durable? vanished)))
    (is (= #{:memory} (:scope vanished)))
    (is (= 2 (count (:successors (m/record s :split)))))))

(deftest local-host-registration-transaction
  (let [s (:state (execute (get new-witnesses :host-readthrough)))
        before (get-in s [:worlds w :obligations])
        processed (execute s [{:t :queued :w w}])
        after (:state processed)]
    (is (= 1 (count before)))
    (is (= 2 (count (get-in after [:worlds w :obligations]))))
    (is (empty? (violations processed)))
    (is (every? #(= w (second (:debtor %))) (vals (get-in after [:worlds w :obligations]))))))

(deftest inherited-activation-converts-bundle
  (let [fixture (cross-world-copy) child [:w 2]
        s (:state (execute (:state fixture) [{:t :t24 :c [:cut 0] :e [:spin 3]} {:t :t36 :w w}]))
        timer (first (for [[o ob] (:obligations (m/wr s child)) :when (= :timer (:kind ob))] o))
        activated (execute s [{:t :t06 :w child :o timer}])
        state (:state activated)]
    (is (= :running (:status (m/run state child r))))
    (is (empty? (violations activated)) (pr-str (violations activated)))
    (is (not-any? #(and (= :bundle (first %)) (= child (second %))) (:fdeps (m/wr state w))))
    (is (some #(and (= [:signal 0] (first %)) (= child (second %))) (:fdeps (m/wr state w))))))

(deftest shared-cuts-complete-protocol
  (let [initial (update-in (:state (execute [following])) [:env :threads] dissoc :host)
        cuts [{:t :t20 :c [:cut 0] :scope root :coordinator :ca
               :participants {:worlds #{w} :components #{[w :a] [v :b]} :systems #{:a}}}
              {:t :t20 :c [:cut 1] :scope [:root v] :coordinator :cb
               :participants {:worlds #{v} :components #{[w :a] [v :b]} :systems #{:b}}}]
        alphabet
        (fn [s]
          (concat
           (for [cut cuts t [:t20 :t20q] :when (not (get-in s [:cuts (:c cut)]))]
             (assoc cut :t t))
           (mapcat (fn [[c cut]]
                     (let [next-w [:w (inc (reduce max (map second (:known-worlds s))))]]
                       (concat
                        (when (m/active-cuts (:phase cut)) [{:t :t25 :c c}])
                        (case (:phase cut)
                          :fenced [{:t :t21 :c c}]
                          :ready [{:t :t22 :c c}]
                          :captured (when (and (< (count (:known-worlds s)) 4) (< (count (:registry s)) 3))
                                      [{:t :t23 :c c :v next-w :k [:cap c] :mode :frozen}])
                          :attached [{:t :t24 :c c :e e}]
                          [])))) (:cuts s))))
        report (bfs initial {:alphabet alphabet :seconds 900 :max-states 20000})]
    (report! :shared-cuts-full report)
    (is (= :exhausted (:status report)))
    (is (empty? (:findings report)) (pr-str (:findings report)))))

(deftest release-waits-for-already-ended-dependencies
  (let [actions [following {:t :t02 :w w :e [:signal 0]} {:t :t04 :w v :e e}
                 {:t :t05 :w v :r r :kind :track :debtor [:entity w [:signal 0]]}
                 {:t :unsubscribe :w v :o [:o 1]}
                 (assoc seal :kind :discard) (assoc prepare-op :steps []) {:t :t29 :op :op}]
        result (execute actions)]
    (check-io/write-report! "minimal-earlier-cleanup.edn"
                            (pr-str {:actions actions :violations (violations result)}))
    (is (not-any? :refusal (:trace result)))
    (is (empty? (violations result)) (pr-str (violations result)))))

(deftest mixed-settlement-search
  (let [initial (:state (execute [(assoc following :systems #{:a :memory})]))
        alphabet #(filter (fn [a] (#{:t26 :t27 :t28 :t29 :t30 :t31 :t32 :t33} (:t a))) (m/enabled %))
        report (bfs initial {:alphabet alphabet :seconds 900 :max-states 50000})]
    (report! :settlement-mixed report)
    (is (= :exhausted (:status report)))
    (is (empty? (:findings report)) (pr-str (:findings report)))))

(deftest inherited-forks-are-read-only-references
  (let [fixture (execute [invoke (assoc following :scope r)
                          {:t :t05 :w w :r r :kind :timer :debtor [:host :executor]}
                          {:t :t19 :w w :v [:w 2] :k [:cap 1] :scope root}])
        s (:state fixture)]
    (is (empty? (violations fixture)) (pr-str (violations fixture)))
    (is (true? (:reference? (m/ent s [:w 2] [:fork v])))))
  (let [fixture (execute (concat [following] (cut-actions :frozen)
                                 [{:t :t26 :caller root :k [:cap 1] :kind :discard :op :references}
                                  {:t :t27 :k [:cap 1] :op :references :steps [] :bases {} :payload :p}
                                  {:t :t29 :op :references} {:t :t36 :w w}]))
        s (:state fixture)]
    (is (not-any? :refusal (:trace fixture)))
    (is (empty? (inv/check s)) (pr-str (inv/check s)))
    (is (empty? (:queue (m/wr s v))))
    (is (= :open (:disposition (m/cap s cap))))))

(deftest conveyed-world-reclamation
  (let [fixture (execute [{:t :t01 :w w :e e :tok [:tok 0]}
                          (assoc invoke :tok [:tok 0]) {:t :t07 :w w :r r}
                          {:t :t08 :w w :e e}])
        cached (execute (:state fixture) [(dissoc (assoc invoke :tok [:tok 0]) :w)])]
    (is (empty? (violations cached)) (pr-str (violations cached))))
  (let [fixture (execute [invoke {:t :t04 :w w :e [:spin 1] :mode :callback}
                          {:t :unsubscribe :w w :o [:o 1]}
                          {:t :t05 :w w :r r :kind :await-once :debtor [:entity w [:spin 1]]}
                          {:t :t07 :w w :r [[:spin 1] 1]}])
        ;; A conveyed host resume still takes its acting world from the obligation.
        o (first (for [[o ob] (:obligations (m/wr (:state fixture) w))
                       :when (= :await-once (:kind ob))] o))
        resumed (execute (:state fixture) [{:t :t35 :th :host :op {:kind :resume :w w :o o}}])]
    (is (some? o))
    (is (nil? (m/ent (:state resumed) w [:spin 1])))
    (is (empty? (violations resumed)) (pr-str (violations resumed)))))

(deftest gc-notification-provenance
  (let [actions [{:t :t01 :w w :e e :tok [:tok 0]} (assoc invoke :tok [:tok 0])]
        s (:state (execute actions))
        premature (m/attempt s {:t :t17 :w w :e e :tok [:tok 0]})
        valid (execute s [{:t :t16 :tok [:tok 0]} {:t :t17 :w w :e e :tok [:tok 0]}
                          {:t :t17 :w w :e e :tok [:tok 0]}])]
    (is (= ::m/reachable-handle (get-in premature [:refusal :error])))
    (is (= s (:state premature)))
    (is (empty? (violations valid)) (pr-str (violations valid)))))

(deftest historical-artifact-replays
  ;; An explicit manifest prevents a missing resource from silently skipping coverage.
  (doseq [name (check-io/read-witness "index.edn")]
    (let [artifact (check-io/read-witness name)
          actions (or (:actions artifact) (get-in artifact [:witness :actions]))
          result (execute actions)
          refused (vec (keep :refusal (:trace result)))]
      (println "LIFETIME REPLAY" name (pr-str (violations result)))
      (is (seq actions) name)
      (if (= name "run5-new-attached-child-settlement.edn")
        (do
          (is (= [::m/unpublished-capability ::m/stale-capability ::m/unfinished]
                 (mapv :error refused)) (pr-str refused))
          (doseq [edge (:trace result) :when (:refusal edge)]
            (is (= (:before edge) (:after edge)) name)))
        (is (empty? refused) (str name " " (pr-str refused))))
      (is (empty? (violations result)) (str name " " (pr-str (violations result)))))))

(deftest pending-start-and-tombstone-protocol
  (let [base (execute [following {:t :t04 :w v :e e}
                       {:t :t05 :w v :r r :kind :await-once :debtor [:entity w [:spin 1]]}])
        s (:state base)]
    (is (nil? (m/ent s w [:spin 1])))
    (is (empty? (:fdeps (m/wr s w))))
    (is (inv/pending-start? s v [:o 1] (get-in s [:worlds v :obligations [:o 1]])))
    (doseq [suffix [[{:t :t37 :w w}]
                    [{:t :t11 :w v :r r} {:t :t37 :w w}]
                    [{:t :t34 :w w} {:t :queued :w v}]]]
      (let [result (execute s suffix)]
        (is (not-any? :refusal (:trace result)))
        (is (empty? (violations result)) (pr-str (violations result))))))
  (let [s (:state (execute [following (assoc seal :kind :discard) (assoc prepare-op :steps []) {:t :t29 :op :op}]))
        cleanup (execute s [{:t :t36 :w w}])]
    (is (= #{:id :lineage :status} (set (keys (m/wr s v)))))
    (is (nil? (m/ent (:state cleanup) w [:fork v])))
    (is (= s (m/enqueue s v {:cancelled :absent})))
    (is (= s (m/enqueue s v {:completion :absent})))
    (is (= s (:state (m/attempt s following))))))

(defn profile-per-state-cost!
  "Three-second sample of the actual BFS worker, without changing its checks."
  []
  (let [worker (Thread/currentThread) running (atom true) samples (atom {})
        sampler (future
                  (while @running
                    (when-let [frame (first (filter #(#{"model.cljc" "invariants.cljc" "bfs_check.clj"} (.getFileName %))
                                                    (.getStackTrace worker)))]
                      (swap! samples update [(.getClassName frame) (.getLineNumber frame)] (fnil inc 0)))
                    (Thread/sleep 10)))
        started (System/nanoTime)
        report (try
                 (bfs (m/init-state {:worlds 1 :generations 1 :scopes 0 :handles 0 :cuts 0
                                     :spins 1 :signals 0 :atoms 0 :filters [:local] :invoke-modes [:callback]})
                      {:seconds 3 :max-states 30000})
                 (finally (reset! running false) @sampler))
        result {:seconds (/ (- (System/nanoTime) started) 1e9)
                :states (:states report) :edges (:edges report)
                :ms-per-discovered-state (* 1000 (/ (:seconds report) (:states report)))
                :us-per-edge (* 1e6 (/ (:seconds report) (:edges report)))
                :samples (reduce + 0 (vals @samples))
                :hotspots (take 12 (sort-by (comp - val) @samples))}]
    (check-io/write-report! "cost.edn" (pr-str result))
    (println "LIFETIME COST" (pr-str result))
    result))

(def search-checks
  '[reduced-complete-search shared-component-cuts settlement-search
    reduction-equivalence smaller-settlement-exhaustion settlement-pareto-fallbacks
    shared-cuts-complete-protocol mixed-settlement-search broad-searches])

(defn run8-suite!
  "One JVM; sequential searches. Every multi-world smoke profile runs once."
  []
  (require 'org.replikativ.spindel.lifetime.generative-check)
  (binding [clojure.test/*report-counters* (ref clojure.test/*initial-report-counters*)]
    (clojure.test/test-vars
     (concat (remove #((set search-checks) (:name (meta %)))
                     (vals (ns-publics 'org.replikativ.spindel.lifetime.bfs-check)))
             (vals (ns-publics 'org.replikativ.spindel.lifetime.generative-check))))
    (println "LIFETIME UNIT-COUNTS" @clojure.test/*report-counters*)
    (doseq [check search-checks]
      (clojure.test/test-vars [(ns-resolve 'org.replikativ.spindel.lifetime.bfs-check check)]))
    (let [counts @clojure.test/*report-counters*]
      (check-io/write-report! "counts.edn" (pr-str counts))
      (println "LIFETIME TOTAL-COUNTS" counts)
      counts)))

(defn -main [& [mode]]
  (let [counts (if (= mode "regressions")
                 (do
                   (require 'org.replikativ.spindel.lifetime.generative-check)
                   (binding [clojure.test/*report-counters* (ref clojure.test/*initial-report-counters*)]
                     (clojure.test/test-vars
                      (concat (remove #((set search-checks) (:name (meta %)))
                                      (vals (ns-publics 'org.replikativ.spindel.lifetime.bfs-check)))
                              (vals (ns-publics 'org.replikativ.spindel.lifetime.generative-check))))
                     (println "LIFETIME UNIT-COUNTS" @clojure.test/*report-counters*)
                     @clojure.test/*report-counters*))
                 (run8-suite!))]
    (shutdown-agents)
    (System/exit (if (zero? (+ (:fail counts) (:error counts))) 0 1))))

(def run4-witnesses
  {:release-fenced-world [(first (cut-actions :frozen)) {:t :t13 :w w :scope root}]
   :released-debtor-l10 (conj (get run3-witnesses :foreign-await-start) {:t :t34 :w w})
   :recreated-incarnation
   [invoke {:t :t01 :w w :r r :e [:spin 1] :tok [:tok 0]}
    {:t :t11 :w w :r r} {:t :t04 :w w :e [:spin 1]}]
   :fork-during-pending-start
   [following {:t :t04 :w v :e e}
    {:t :t05 :w v :r r :kind :await-once :debtor [:entity w [:spin 1]]}
    {:t :t19 :w v :v [:w 2] :k [:cap 1] :scope [:root v]}]
   :cancelled-start-on-sealed
   [following {:t :t04 :w w :e e}
    {:t :t05 :w w :r r :kind :await-once :debtor [:entity v [:spin 1]]}
    (assoc seal :kind :discard) {:t :t37 :w v}]
   :completion-before-tombstone
   [following {:t :t04 :w v :e e}
    {:t :t05 :w v :r r :kind :await-once :debtor [:entity w [:spin 1]]}
    {:t :t37 :w w} {:t :t07 :w w :r [[:spin 1] 1]} {:t :t34 :w w}]
   :cut-drain-work
   [invoke (first (cut-actions :frozen))
    {:t :t21 :c [:cut 0] :body {:t :t05 :w w :r r :kind :timer :debtor [:host :executor]}}]})

(deftest run4-normative-counterexamples
  (doseq [[name actions] run4-witnesses]
    (let [result (execute actions) bad (violations result)]
      (check-io/write-report! (str "new-" (clojure.core/name name) ".edn")
                              (pr-str {:actions actions :violations bad :clean? (empty? bad)
                                       :refusals (vec (keep :refusal (:trace result)))}))
      (println "LIFETIME RUN4-WITNESS" name (pr-str bad))
      (is (not-any? :refusal (:trace result)) (pr-str (keep :refusal (:trace result))))
      (is (empty? bad) (str name " " (pr-str bad))))))

(deftest cut-footprint-negative-controls
  (let [before (:state (execute (butlast (cut-actions :frozen))))
        action (last (cut-actions :frozen)) after (m/step before action)
        corruptions [(assoc-in after [:worlds w :entities :unrelated] (m/row :spin root))
                     (update after :registry conj :unrelated)
                     (assoc-in after [:env :threads :host :run] :unrelated)
                     (assoc-in after [:durable :records :unrelated] {})]]
    (is (empty? (inv/cut-footprint-errors before action after)))
    (doseq [corrupt corruptions]
      (is (some #(= :TL6 (:id %)) (inv/edge-check {:before before :action action :after corrupt}))))))

(deftest release-request-and-cleanup-edges
  (let [result (execute [invoke following {:t :t04 :w v :e e} {:t :t34 :w w}])
        deliveries (filter #(and (= :host-delivery (:event %)) (= ::m/released (:value %)))
                           (get-in result [:state :events]))]
    (is (not-any? :refusal (:trace result)))
    (is (empty? (violations result)) (pr-str (violations result)))
    (is (= #{[:o 0] [:o 1]} (set (map :o deliveries)))))
  (let [base (:state (execute [following {:t :t34 :w w}]))
        request (execute base [{:t :arrival :w w :event {:start-for e :creditor-world v :o :gone}}])
        host (execute base [{:t :arrival :w w :event {:register-host :host-request :e e}}])]
    (is (empty? (violations request)) (pr-str (violations request)))
    (is (inv/queued? (:state request) v :cancelled :gone))
    (is (empty? (violations host)) (pr-str (violations host)))
    (is (some #(and (= :host-request (:o %)) (= ::m/released (:value %)))
              (get-in host [:state :events])))
    (doseq [event [{:cancelled :gone} {:fdep-ended [:missing v :gone]} {:completion e}]]
      (is (= base (:state (execute base [{:t :arrival :w w :event event}]))))))
  (let [result (execute [{:t :arrival :w w :event {:cancelled :gone}} {:t :t36 :w w}])]
    (is (not-any? :refusal (:trace result)))
    (is (empty? (violations result)) (pr-str (violations result)))
    (is (empty? (:queue (m/wr (:state result) w))))))

(deftest ownerless-settling-fork
  (let [result (execute [{:t :t12 :w w :scope [:scope 0] :parent root}
                         (assoc following :scope [:scope 0])
                         (assoc seal :caller [:scope 0])
                         {:t :t13 :w w :scope [:scope 0]}])
        s (:state result)]
    (is (not-any? :refusal (:trace result)))
    (is (nil? (:owner (m/ent s w [:fork v]))))
    (is (= #{:settle} (m/reasons s w [:fork v])))
    (is (empty? (violations result)) (pr-str (violations result)))))

(deftest rejected-start-reports-released
  (let [s (:state (execute (get run4-witnesses :cancelled-start-on-sealed)))
        after (m/step s {:t :t36 :w w})]
    ;; The preceding rejection window is checked separately; this checks the
    ;; specified error payload at local delivery.
    (is (some #(and (= :resume (:event %)) (= ::m/released (:value %))) (:events after)))
    (is (empty? (inv/check after)) (pr-str (inv/check after)))))

(deftest tombstone-in-flight-negative-controls
  (let [s (:state (execute (get new-witnesses :foreign-release)))
        corrupt (update-in s [:worlds v :queue] #(vec (remove :cancelled %)))]
    (is (empty? (inv/l05 s)))
    (is (empty? (inv/l20 s)))
    (is (seq (inv/l05 corrupt)))
    (is (seq (inv/l20 corrupt))))
  (let [s (:state (execute [following {:t :t02 :w w :e [:signal 0]} {:t :t04 :w v :e e}
                            {:t :t05 :w v :r r :kind :track :debtor [:entity w [:signal 0]]}
                            {:t :unsubscribe :w v :o [:o 1]}
                            (assoc seal :kind :discard) (assoc prepare-op :steps []) {:t :t29 :op :op}]))]
    (is (empty? (inv/check s)) (pr-str (inv/check s)))
    (doseq [key [:fdep-ended :fork-released]]
      (let [corrupt (update-in s [:worlds w :queue] #(vec (remove key %)))]
        (is (seq (inv/l04 corrupt)))
        (is (seq (inv/l20 corrupt)))))
    (is (seq (inv/l20 (assoc-in s [:worlds v :entities] {}))))))

(deftest lost-world-capabilities-require-restart
  (let [s (:state (execute [(assoc following :systems #{:a :memory}) {:t :t31}]))
        actions [seal
                 {:t :t32 :k cap :op :transfer :successor [:cap 1] :holder :other}
                 {:t :t33 :k cap :op :partition
                  :successors [{:k [:cap 1] :scope #{:a}} {:k [:cap 2] :scope #{:memory}}]}]]
    (doseq [a actions]
      (let [{after :state refusal :refusal} (m/attempt s a)]
        (is (= ::m/missing-world (:error refusal)))
        (is (= s after))))
    (let [result (execute s [{:t :t31 :phase :restart}])]
      (is (empty? (violations result)) (pr-str (violations result)))
      (is (= :settling (:disposition (m/cap (:state result) cap))))
      (is (= #{cap} (set (keys (get-in result [:state :durable :caps]))))))))

(deftest phase-evidence-negative-controls
  (let [s (:state (execute (get run3-witnesses :foreign-await-start)))
        corrupt (assoc-in s [:worlds w :queue] [])
        both (m/enqueue s v {:cancelled [:o 1]})]
    (is (empty? (inv/check s)))
    (is (seq (inv/l05 corrupt)))
    (is (seq (inv/l10 corrupt)))
    (is (seq (inv/l10 both))))
  (let [s (:state (execute (get run4-witnesses :cancelled-start-on-sealed)))
        corrupt (assoc-in s [:worlds w :queue] [])]
    (is (empty? (inv/check s)))
    (is (seq (inv/l05 corrupt)))
    (is (seq (inv/l10 corrupt)))))

(deftest pending-copy-admission-and-activation
  (let [prefix (get run4-witnesses :fork-during-pending-start)
        u [:w 2]
        result (execute (concat prefix [{:t :t37 :w w} {:t :t37 :w w}]))
        s (:state result)]
    (is (not-any? :refusal (:trace result)))
    (is (empty? (violations result)) (pr-str (violations result)))
    (is (contains? (:fdeps (m/wr s w)) [[:spin 1] v [:o 1]]))
    (is (contains? (:fdeps (m/wr s w)) [:bundle u #{[:spin 1]}]))
    (let [resumed (execute s [{:t :t07 :w w :r [[:spin 1] 1] :value :payload}
                              {:t :queued :w u} {:t :queued :w v}])]
      (is (empty? (violations resumed)) (pr-str (violations resumed)))
      (is (= :running (:status (m/run (:state resumed) u r))))
      (is (some #(and (= :resume (:event %)) (= :payload (:value %)))
                (mapcat (comp :events :after) (:trace resumed)))))))

(deftest completion-cancellation-order
  (let [prefix (get run4-witnesses :completion-before-tombstone)
        result (execute (concat prefix [{:t :queued :w v} {:t :queued :w v}]))
        s (:state result)]
    (is (not-any? :refusal (:trace result)))
    (is (empty? (violations result)) (pr-str (violations result)))
    (is (= :running (:status (m/run s v r))))
    (is (nil? (get-in s [:worlds v :obligations [:o 1]])))
    (is (= 1 (count (filter #(and (= :resume (:event %)) (= v (:world %)))
                            (mapcat (comp :events :after) (:trace result))))))
    (is (some #(and (= :resume (:event %)) (= :result (:value %)))
              (:events (:after (nth (:trace result) (count prefix))))))))

(deftest token-coverage-insertion-paths
  (let [prefix [invoke {:t :t01 :w w :r r :e [:spin 1] :tok [:tok 0]}
                {:t :t01 :w w :r r :e [:spin 1] :tok [:tok 1]} {:t :t11 :w w :r r}]
        variants [[{:t :t04 :w w :e [:spin 1] :tok [:tok 1]}]
                  [(assoc invoke :e [:spin 2])
                   {:t :t01 :w w :r [[:spin 2] 1] :e [:spin 1]}]
                  [following {:t :t04 :w v :e e}
                   {:t :t05 :w v :r r :kind :await-once :debtor [:entity w [:spin 1]]}
                   {:t :t37 :w w}]]]
    (doseq [suffix variants]
      (let [result (execute (concat prefix suffix))]
        (is (not-any? :refusal (:trace result)))
        (is (empty? (violations result)) (pr-str (violations result)))
        (is (= #{[:tok 0] [:tok 1]} (:tokens (m/ent (:state result) w [:spin 1]))))))))

(deftest abort-before-participant-release
  (doseq [n [1 2 3 4]]
    (let [result (execute (concat (take n (cut-actions :frozen)) [{:t :t34 :w w}]))
          s (:state result)]
      (is (not-any? :refusal (:trace result)))
      (is (empty? (violations result)) (pr-str (violations result)))
      (is (= :failed (get-in s [:cuts [:cut 0] :phase])))
      (is (= :released (:status (m/wr s w))))
      (is (empty? (get-in s [:env :threads :coordinator :excl-permits])))
      (is (nil? (m/wr s [:w 2]))))))

(def run5-witnesses
  {:debtor-cancel [invoke
                   {:t :t05 :w w :r r :kind :await-once :debtor [:entity w [:spin 1]]}
                   following {:t :t11 :w w :r [[:spin 1] 1]}]
   :copy-cancelling (conj (get run4-witnesses :released-debtor-l10)
                          {:t :t19 :w v :v [:w 2] :k [:cap 1] :scope [:root v]})
   :independent-invoke [invoke {:t :t01 :w w :r r :e [:spin 1] :tok [:tok 0]}
                        {:t :t04 :w w :e [:spin 1] :tok [:tok 0]}
                        {:t :t11 :w w :r r}]})

(deftest run5-normative-counterexamples
  (doseq [[name actions] run5-witnesses]
    (let [result (execute actions) s (:state result)]
      (println "LIFETIME RUN5-WITNESS" name (pr-str (violations result)))
      (is (not-any? :refusal (:trace result)))
      (is (empty? (violations result)) (str name " " (pr-str (violations result))))
      (case name
        :debtor-cancel
        (do (is (inv/queued? s v :cancelled [:o 1]))
            (is (empty? (:fdeps (m/wr s w))))
            (is (empty? (:releasing (m/wr s w)))))
        :copy-cancelling
        (is (= (map #(dissoc % :seq) (filter :cancelled (:queue (m/wr s v))))
               (map #(dissoc % :seq) (filter :cancelled (:queue (m/wr s [:w 2]))))))
        :independent-invoke
        (do (is (not-any? m/work? (vals (:runs (m/wr s w)))))
            (is (some #(and (= :host-delivery (:event %)) (= ::m/cancelled (:value %)))
                      (:events s))))))))

(deftest cut-drain-world-transactions
  (let [s (:state (execute (conj (get run3-witnesses :foreign-await-start)
                                 (first (cut-actions :frozen)))))
        a {:t :t21 :c [:cut 0]} after (m/step s a)
        corrupt (assoc-in after [:worlds v :entities :unrelated] (m/row :spin [:root v]))
        wrong-body (m/attempt s (assoc a :body {:t :t07 :w v :r r}))]
    (is (empty? (inv/check after)))
    (is (empty? (inv/edge-check {:before s :action a :after after})))
    (is (= :running (:status (m/run after w [[:spin 1] 1]))))
    (is (some #(= :TL6 (:id %)) (inv/edge-check {:before s :action a :after corrupt})))
    (is (= s (:state wrong-body)))
    (is (= ::m/not-admitted (get-in wrong-body [:refusal :error])))))

(deftest canonical-child-before-parent
  (let [s (:state (execute [(assoc invoke :e [:spin 3] :mode :deref)
                            (assoc invoke :e [:spin 1])
                            {:t :t01 :w w :r [[:spin 3] 1] :e e :tok [:tok 0]}
                            following {:t :t04 :w v :e e}]))
        c (m/canonical s)]
    (is (= c (m/canonical c)))
    (doseq [changed [(assoc-in s [:worlds w :entities [:spin 1] :result] :different)
                     (assoc-in s [:worlds w :obligations [:o 0] :slot] :consumed)
                     (assoc s :resume-monitor #{[:slot w r [:o 0]]})
                     (assoc s :sleep #{invoke})]]
      (is (not= c (m/canonical changed))))))

(deftest attached-child-settlement-before-admission
  (let [result (execute (butlast (cut-actions :frozen)))
        s (:state result) k [:cap 1]
        attempts [(assoc seal :k k :kind :discard)
                  {:t :t32 :k k :successor [:cap 2] :holder root :op :transfer}
                  {:t :t33 :k k :op :partition
                   :successors [{:k [:cap 2] :scope #{:a}} {:k [:cap 3] :scope #{:b}}]}]]
    (is (empty? (violations result)))
    (is (false? (:published? (m/cap s k))))
    (doseq [a attempts]
      (let [{after :state refusal :refusal} (m/attempt s a)]
        (is (= ::m/unpublished-capability (:error refusal)))
        (is (= s after))))
    (is (not-any? #(and (#{:t26 :t32 :t33} (:t %)) (= k (:k %))) (m/enabled s)))
    (is (seq (inv/l22 (assoc-in s (conj (m/cap-path s k) :published?) true))))
    (let [published (execute s [(last (cut-actions :frozen))])
          aborted (execute s [{:t :t25 :c [:cut 0]}])]
      (is (true? (:published? (m/cap (:state published) k))))
      (is (nil? (m/cap (:state aborted) k)))
      (is (empty? (violations published)))
      (is (empty? (violations aborted))))))

(deftest owner-release-cascades
  (doseq [[setup ending]
          [[[invoke {:t :t01 :w w :r r :e [:spin 1] :tok [:tok 0]}
             {:t :t04 :w w :e [:spin 1] :tok [:tok 0]}
             {:t :t07 :w w :r r} {:t :t09 :w w :e e}]
            {:t :t07 :w w :r [e 2]}]
           [[{:t :t12 :w w :scope [:scope 0] :parent root}
             (assoc invoke :scope [:scope 0])
             {:t :t01 :w w :r r :e [:spin 1] :tok [:tok 0]}
             {:t :t04 :w w :e [:spin 1] :tok [:tok 0]}]
            {:t :t13 :w w :scope [:scope 0]}]]]
    (let [prefix (execute setup) s (:state prefix)
          result (execute s [ending]) child [:spin 1]]
      (is (= r (:owner (m/ent s w child))))
      (is (= root (:owner (m/run s w [child 1]))))
      (is (not-any? :refusal (concat (:trace prefix) (:trace result))))
      (is (not-any? #(and (= child (:spin %)) (m/work? %))
                    (vals (:runs (m/wr (:state result) w)))))
      (is (empty? (violations prefix)) (pr-str (violations prefix)))
      (is (empty? (violations result)) (pr-str (violations result))))))

(deftest cancelling-cut-copy-preserves-payload
  (let [prefix (get run4-witnesses :cancelled-start-on-sealed)
        cut [{:t :t20 :c [:cut 0] :scope root
              :participants {:worlds #{w} :components #{[w :sci]} :systems #{:a}}}
             {:t :t21 :c [:cut 0]} {:t :t22 :c [:cut 0]}
             {:t :t23 :c [:cut 0] :v [:w 2] :k [:cap 1] :mode :frozen}]
        result (execute (concat (butlast prefix) (take 2 cut) [(last prefix)] (drop 2 cut)))
        s (:state result) u [:w 2]]
    (is (not-any? :refusal (:trace result)))
    (is (empty? (violations result)) (pr-str (violations result)))
    (is (= ::m/released (:value (first (filter :cancelled (:queue (m/wr s u)))))))
    (is (seq (inv/l05 (update-in s [:worlds u :queue] #(vec (remove :cancelled %))))))
    (is (seq (inv/l10 (update-in s [:worlds u :queue] #(vec (remove :cancelled %))))))))

(deftest owner-release-completed-cache
  (let [actions [{:t :t02 :w w :e [:signal 0]} invoke
                 {:t :t05 :w w :r r :kind :track :debtor [:entity w [:signal 0]]}
                 {:t :t01 :w w :r r :e [:spin 1] :tok [:tok 0]}
                 {:t :t04 :w w :e [:spin 1] :tok [:tok 0]}
                 {:t :t07 :w w :r [[:spin 1] 1] :value :cached}
                 {:t :t11 :w w :r r}]
        result (execute actions) s (:state result)]
    (is (not-any? :refusal (:trace result)))
    (is (empty? (violations result)) (pr-str (violations result)))
    (is (= :cached (:result (m/ent s w [:spin 1]))))
    (is (true? (:dirty? (m/ent s w [:spin 1]))))
    (is (empty? (:obligations (m/wr s w)))))
  (let [result (execute [{:t :t12 :w w :scope [:scope 0] :parent root}
                         {:t :t02 :w w :scope [:scope 0] :e [:signal 0]}
                         invoke {:t :t05 :w w :r r :kind :track :debtor [:entity w [:signal 0]]}
                         {:t :t13 :w w :scope [:scope 0]}])]
    (is (not-any? :refusal (:trace result)))
    (is (empty? (violations result)) (pr-str (violations result)))
    (is (nil? (m/ent (:state result) w [:signal 0])))))

(deftest run6-normative-counterexamples
  (doseq [name ["run6-F50.edn" "run6-F51.edn"]]
    (let [{:keys [actions]} (check-io/read-witness name)
          result (execute actions)
          refused (vec (keep :refusal (:trace result)))]
      (if (= name "run6-F50.edn")
        (do (is (= [::m/cut-phase] (mapv :error refused)))
            (is (= :failed (get-in result [:state :cuts [:cut 0] :phase])))
            (is (= :sealed (:status (m/wr (:state result) v))))
            (is (= :fenced (:admission (m/wr (:state result) v)))))
        (do (is (empty? refused))
            (is (empty? (:queue (m/wr (:state result) w))))
            (is (= [:cancelling] (inv/obligation-phases (:state result) v [:o 1]
                                                        (get-in result [:state :worlds v :obligations [:o 1]]))))))
      (doseq [edge (:trace result) :when (:refusal edge)]
        (is (= (:before edge) (:after edge))))
      (is (empty? (violations result)) (str name " " (pr-str (violations result)))))))

(def quiescent-fence (assoc (first (cut-actions :frozen)) :t :t20q))

(deftest run7-artifact-replays
  (doseq [name (check-io/read-witness "run7/index.edn")]
    (let [{:keys [actions initial-options refusals negative-control?]} (check-io/read-witness name)
          result (execute (m/init-state initial-options) actions)]
      (is (seq actions) name)
      (is (= refusals (mapv :error (keep :refusal (:trace result)))) name)
      (doseq [edge (:trace result) :when (:refusal edge)]
        (is (= (:before edge) (:after edge)) name))
      (if negative-control?
        (do (is (seq (inv/l10 (:before (last (:trace result))))))
            (is (empty? (inv/check (:state result))))
            (is (empty? (inv/edge-check (last (:trace result)))))
            (is (nil? (m/current (:state result) w [:spin 1]))))
        (is (empty? (violations result)) (str name " " (pr-str (violations result)))))
      (is (not-any? #(= :t21 (:t %)) actions) name))))

(deftest quiescent-refusals-have-diagnostics
  (let [running (:state (execute [invoke]))
        queued (:state (execute [{:t :t02 :w w :e [:signal 0]}
                                 {:t :arrival :w w :event {:completion [:signal 0] :debtor-world w}}]))
        native (:state (execute [invoke {:t :t05 :w w :r r :kind :external :debtor [:host :native]}]))]
    (doseq [[state field] [[running :running] [queued :admitted] [native :native]]]
      (let [result (m/attempt state quiescent-fence)]
        (is (= ::m/not-quiescent (get-in result [:refusal :error])))
        (is (seq (get-in result [:refusal field])))
        (is (= state (:state result)))
        (is (empty? (:cuts (:state result))))
        (is (= :open (:admission (m/wr (:state result) w)))))))
  (doseq [state [(m/init-state) (:state (execute [invoke]))]]
    (let [p1 (-> state (m/step (assoc quiescent-fence :t :t20))
                 (m/step {:t :t25 :c [:cut 0]}))]
      ;; Atomic refusal contracts preserve all semantic rows. The discarded
      ;; coordinator record and allocation counter are only instrumentation.
      (is (= (:worlds state) (:worlds p1)))
      (is (= (get-in state [:env :native]) (get-in p1 [:env :native])))
      (is (empty? (inv/check p1))))))

(deftest quiescent-trace-refines-zero-drain-p1
  (doseq [mode [:frozen :materialized] terminal [:t24 :t25]]
    (let [setup [invoke {:t :t05 :w w :r r :kind :timer :debtor [:host :executor]}]
          arrival {:t :arrival :w w :event {:completion [:spin 1] :debtor-world w :value :late}}
          finish [{:t :t22 :c [:cut 0]} {:t :t23 :c [:cut 0] :v [:w 2] :k [:cap 1] :mode mode}
                  {:t terminal :c [:cut 0]}]
          q (execute (concat setup [(assoc quiescent-fence :mode mode) arrival] finish))
          p1 (execute (concat setup [(assoc quiescent-fence :t :t20 :mode mode)
                                     {:t :t21 :c [:cut 0]} arrival] finish))
          readiness (nth (:trace p1) (inc (count setup)))]
      (is (not-any? :refusal (:trace q)))
      (is (not-any? :refusal (:trace p1)))
      (is (= (:worlds (:before readiness)) (:worlds (:after readiness))))
      (is (empty? (:events (:after readiness))))
      (is (= (:state p1) (update-in (:state q) [:cuts [:cut 0]] dissoc :protocol)))
      (is (empty? (violations p1)))
      (is (empty? (violations q)))
      (is (= :inherited (:status (m/run (:after (nth (:trace q) (+ (count setup) 3))) [:w 2] r)))))))

(deftest quiescent-fence-and-readiness-negative-controls
  (let [state (:state (execute [quiescent-fence]))
        event {:cancelled [:o 99] :value ::m/released}
        arrived (:state (execute state [{:t :arrival :w w :event event}
                                        {:t :arrival :w w :event event}]))
        bad (-> arrived (assoc-in [:worlds w :queue] [(assoc event :seq 1)])
                (assoc-in [:env :outside] []))]
    (is (empty? (:queue (m/wr arrived w))))
    (is (= 1 (count (get-in arrived [:env :outside]))))
    (is (empty? (inv/check arrived)))
    (is (seq (inv/l22 bad)))
    (is (= ::m/no-drain (get-in (m/attempt state {:t :t21 :c [:cut 0]}) [:refusal :error])))
    (doseq [t [:t06 :t08 :t09 :t36 :t37 :queued]]
      (is (= ::m/not-admitted (get-in (m/attempt state {:t t :w w}) [:refusal :error]))))
    (let [released (:state (execute arrived [{:t :t25 :c [:cut 0]}]))]
      (is (empty? (get-in released [:env :outside])))
      (is (= [event] (mapv #(dissoc % :seq) (:queue (m/wr released w)))))))
  (let [state (:state (execute [quiescent-fence]))
        running (assoc-in state [:worlds w :runs r] {:spin e :owner root :status :running})
        native (assoc-in state [:env :native :n] {:owner [w r] :state :running})]
    (is (seq (inv/l22 running)))
    (is (seq (inv/l22 native)))
    (is (seq (inv/l22 (assoc-in state [:cuts [:cut 0] :phase] :fenced))))))

(deftest seal-aborts-all-cut-phases
  (doseq [protocol [:t20 :t20q] phase [:fenced :ready :captured :attached]
          :when (not (and (= :t20q protocol) (= :fenced phase)))]
    (let [fence (assoc quiescent-fence :t protocol :scope [:root v]
                       :participants {:worlds #{v} :components #{[v :sci]} :systems #{:a}})
          advance (case phase :fenced [] :ready [{:t :t21 :c [:cut 0]}]
                        :captured [{:t :t21 :c [:cut 0]} {:t :t22 :c [:cut 0]}]
                        :attached [{:t :t21 :c [:cut 0]} {:t :t22 :c [:cut 0]}
                                   {:t :t23 :c [:cut 0] :v [:w 2] :k [:cap 1] :mode :frozen}])
          actions (concat [following fence] (if (= :t20q protocol) (remove #(= :t21 (:t %)) advance) advance) [seal])
          result (execute actions) state (:state result)]
      (is (not-any? :refusal (:trace result)))
      (is (empty? (violations result)) (pr-str (violations result)))
      (is (= :failed (get-in state [:cuts [:cut 0] :phase])))
      (is (= :sealed (:status (m/wr state v))))
      (is (= :fenced (:admission (m/wr state v))))
      (is (empty? (get-in state [:env :threads :coordinator :excl-permits])))
      (is (nil? (m/wr state [:w 2])))
      (is (nil? (m/cap state [:cap 1]))))))

(deftest cut-release-never-reopens-sealed-participants
  ;; Defence in depth, separate from T26's mandatory abort. Deliberately
  ;; construct a sealed participant while retaining the active cut record.
  (doseq [terminal [:t24 :t25]]
    (let [state (:state (execute (butlast (cut-actions :frozen))))
          sealed (-> state (assoc-in [:worlds w :status] :sealed)
                     (assoc-in [:worlds w :seal-seq] 0))
          result (m/step sealed {:t terminal :c [:cut 0]})]
      (is (= :sealed (:status (m/wr result w))))
      (is (= :fenced (:admission (m/wr result w))))
      (is (empty? (inv/l16 result))))))

(deftest run7-normative-counterexamples
  (doseq [file ["run7/F52.edn" "run7/F53.edn" "run7/F54.edn"]]
    (let [{:keys [actions target]} (check-io/read-witness file)
          result (execute actions)]
      (is (not-any? :refusal (:trace result)))
      (is (empty? (violations result)) (str file " " (pr-str (violations result)))))))

(deftest pending-start-cancellation-is-keyed
  (let [child [:w 2]
        setup [following {:t :t04 :w v :e e}
               {:t :t05 :w v :r r :kind :await-once :debtor [:entity w [:spin 1]]}
               {:t :t04 :w v :e [:spin 2]}
               {:t :t05 :w v :r [[:spin 2] 1] :kind :await-once :debtor [:entity w [:spin 3]]}
               {:t :t19 :w v :v child :k [:cap 1] :scope [:root v]}
               {:t :t04 :w w :e [:spin 1]}
               {:t :t11 :w w :r [[:spin 1] 1]}]
        result (execute setup) state (:state result)]
    (is (not-any? :refusal (:trace result)))
    (is (empty? (violations result)) (pr-str (violations result)))
    (is (= 2 (count (:queue (m/wr state w)))))
    (is (every? #(= [:spin 3] (:start-for %)) (:queue (m/wr state w))))
    (doseq [target [v child]]
      (is (= [:cancelling] (inv/obligation-phases state target [:o 1]
                                                  (get-in state [:worlds target :obligations [:o 1]]))))
      (is (= [:pending-start] (inv/obligation-phases state target [:o 3]
                                                     (get-in state [:worlds target :obligations [:o 3]])))))))

(deftest stale-start-never-admits-or-restarts
  (let [setup [following {:t :t04 :w v :e e}
               {:t :t05 :w v :r r :kind :await-once :debtor [:entity w [:spin 1]]}]
        request {:start-for [:spin 1] :creditor-world v :o [:o 1]}
        admitted (:state (execute (conj setup {:t :t37 :w w})))
        consumed (assoc-in admitted [:worlds v :obligations [:o 1] :slot] :consumed)
        gone (update-in admitted [:worlds v :obligations] dissoc [:o 1])]
    ;; Obsolete requests are corruption controls, not legal phase-preserving
    ;; traces. T37 must discard them without any body entry or new authority.
    (doseq [state [admitted consumed gone]]
      (let [queued (m/enqueue state w request)
            after (m/step queued {:t :t37 :w w})]
        (is (= (:runs (m/wr state w)) (:runs (m/wr after w))))
        (is (= (:fdeps (m/wr state w)) (:fdeps (m/wr after w))))
        (is (empty? (:queue (m/wr after w))))
        (is (empty? (:events after)))))))

(deftest held-phase-evidence-is-required
  (doseq [[file prefix-count expected] [["run7/p1q-held-start.edn" 4 :pending-start]
                                        ["run7/F52.edn" 6 :cancelling]]]
    (let [actions (:actions (check-io/read-witness file))
          result (execute (take prefix-count actions)) state (:state result)
          [world o ob] (first (for [[world o ob] (inv/obligations state)
                                    :when (= :run (first (:creditor ob)))] [world o ob]))
          missing (assoc-in state [:env :outside] [])]
      (is (not-any? :refusal (:trace result)))
      (is (empty? (violations result)))
      (is (= [expected] (inv/obligation-phases state world o ob)))
      (is (seq (inv/l10 missing)))
      (is (not= [expected] (inv/obligation-phases missing world o ob))))))

(deftest held-control-traces-refine-zero-drain-p1
  ;; Refinement must use the same admission rule for ordinary and control
  ;; envelopes. The resolved witnesses must agree under both protocols.
  (doseq [file ["run7/F52.edn" "run7/F53.edn"]]
    (let [actions (:actions (check-io/read-witness file))
          expanded (mapcat #(if (= :t20q (:t %))
                              [(assoc % :t :t20) {:t :t21 :c (:c %)}] [%]) actions)
          q (execute actions) p1 (execute expanded)]
      (is (not-any? :refusal (:trace q)))
      (is (not-any? :refusal (:trace p1)))
      (is (= (:state p1) (update-in (:state q) [:cuts [:cut 0]] dissoc :protocol)))
      (is (= (violations p1) (violations q))))))

(deftest run8-artifact-replays
  (doseq [file (check-io/read-witness "run8/index.edn")]
    (let [{:keys [actions]} (check-io/read-witness file)
          result (execute actions)]
      (is (seq actions) file)
      (let [refused (filter :refusal (:trace result))
            empty-at (case file
                       "run8/F55.edn" 8
                       "run8/join-admitted.edn" 7
                       "run8/rollback-pending-join.edn" 8 nil)]
        (is (= (if empty-at [::m/empty-queue] []) (mapv (comp :error :refusal) refused)) file)
        (when empty-at
          (is (= [empty-at] (keep-indexed #(when (:refusal %2) %1) (:trace result))) file))
        (doseq [edge refused] (is (= (:before edge) (:after edge)) file)))
      ;; Finding metadata records the original counterexample; run-8 triage
      ;; moved request emission to T24. Keep every normative assertion enabled.
      (is (empty? (violations result)) (str file " " (pr-str (violations result)))))))

(deftest run8-join-request-protocol
  (let [actions (:actions (check-io/read-witness "run8/cancel-after-capture.edn"))
        result (execute (take 9 actions)) state (:state result) child [:w 2]
        request (first (:queue (m/wr state v)))
        child-ob (get-in state [:worlds child :obligations [:o 1]])]
    (is (empty? (violations result)))
    (is (= child (:join-bundle request)))
    (is (= #{[:spin 1]} (:debtors request)))
    (is (= {[:o 1] {:debtor [:spin 1] :source-world w :source-o [:o 1]}} (:members request)))
    (is (empty? (:fdeps (m/wr state v))))
    (is (= [:pending-start] (inv/obligation-phases state child [:o 1] child-ob)))
    (is (seq (inv/l10 (assoc-in state [:worlds v :queue] []))))
    (let [corrupt (update-in state [:worlds v :fdeps] conj [:bundle child #{[:spin 1]}])]
      (is (seq (inv/l10 corrupt))))
    ;; T24 may enqueue the exact requests, never write a foreign dependency.
    (let [before (:before (last (:trace result)))
          illegal (update-in state [:worlds v :fdeps] conj [:bundle child #{[:spin 1]}])]
      (is (seq (inv/cut-footprint-errors before (last (take 9 actions)) illegal)))))
  (let [actions (:actions (check-io/read-witness "run8/join-admitted.edn"))
        attached (:state (execute (concat (take 7 actions) [{:t :t24 :c [:cut 0]}])))
        child [:w 2]
        admitted (execute attached [{:t :t36 :w v}])]
    (is (= #{[:bundle child #{[:spin 1]}] [[:spin 1] w [:o 1]]}
           (:fdeps (m/wr (:state admitted) v))))
    (is (empty? (violations admitted)))
    (let [obsolete (m/enqueue (:state admitted) v (dissoc (first (:queue (m/wr attached v))) :seq))
          after (m/step obsolete {:t :t36 :w v})]
      (is (= (:fdeps (m/wr (:state admitted) v)) (:fdeps (m/wr after v)))))))

(deftest run8-copy-basis-evidence
  (let [actions (:actions (check-io/read-witness "run7/F52.edn"))
        captured (:state (execute (take 7 actions)))
        child [:w 2]
        attach (last actions)
        held (get-in captured [:cuts [:cut 0] :basis w :held])
        copied (m/step captured attach)]
    (is (= (get-in captured [:env :outside]) held))
    (is (= :cancelling (get-in captured [:cuts [:cut 0] :basis w :copy-evidence [:o 1] :phase])))
    (is (= [{:cancelled [:o 1] :seq 1}] (:queue (m/wr copied child))))
    ;; Removing the live mailbox after capture must not change the copied value.
    (is (= (m/wr copied child)
           (m/wr (m/step (assoc-in captured [:env :outside] []) attach) child)))
    (is (= (get-in captured [:env :outside]) (get-in copied [:env :outside])))
    (is (seq (inv/l22 (assoc-in copied [:worlds child :queue] []))))
    (is (seq (inv/l22 (assoc-in copied [:worlds child :releasing] #{[[:spin 1] v [:o 1]]}))))))

(deftest run8-fresh-start-retires-inherited
  (let [timer-actions (take 3 (:actions (check-io/read-witness "run7/F54.edn")))
        source (:state (execute timer-actions))
        starter [{:t :t04 :w v :e [:spin 2]}
                 {:t :t05 :w v :r [[:spin 2] 1] :kind :await-once :debtor [:entity v e]}]
        foreign [{:t :t04 :w w :e [:spin 2]}
                 {:t :t05 :w w :r [[:spin 2] 1] :kind :await-once :debtor [:entity v e]}
                 {:t :t37 :w v}]]
    (doseq [actions [[{:t :t04 :w v :e e}] starter foreign]]
      (let [result (execute source actions) state (:state result)
            resumed (m/step state {:t :t06 :w v :o [:o 1]})]
        (is (not-any? :refusal (:trace result)))
        (is (empty? (violations result)) (pr-str (violations result)))
        (is (nil? (m/run state v r)))
        (is (= [e 2] (m/current state v e)))
        (is (nil? (get-in state [:worlds v :obligations [:o 1]])))
        (is (nil? (m/ent state v [:timer [:o 1]])))
        (is (= (m/wr state v) (m/wr resumed v)))
        (is (= :parked (:status (m/run state w r))))))))

(deftest run8-reissued-envelope-sequence
  (let [old (:actions (check-io/read-witness "run7/F52.edn"))
        arrivals (for [value [:first :second :third]]
                   {:t :arrival :w w :event {:completion [:spin 1] :debtor-world v :value value}})
        result (execute (concat (take 5 old) arrivals [(nth old 6) (last old)]))
        child [:w 2] state (:state result)
        after (m/enqueue state child {:completion [:spin 1] :debtor-world v :value :later})
        events (inv/queued-events after child)]
    (is (not-any? :refusal (:trace result)))
    (is (empty? (violations result)) (pr-str (violations result)))
    (is (= [:first :second :third :later] (mapv :value events)))
    (is (= [1 2 3 4] (mapv :seq events)))))
