(ns org.replikativ.spindel.lifetime.run10-check
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.lifetime.bfs-check :as b]
            [org.replikativ.spindel.lifetime.check-io :as io]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.run9-check :as r9]))

(def f57-files
  ["run9/F57-before-attach.edn" "run9/F57-after-attach.edn"
   "run9/F57-admitted-release.edn" "run9/F57-admitted-after-attach.edn"])

(deftest run10-artifacts
  (doseq [file (io/read-witness "run10/index.edn")]
    (let [result (b/execute (r9/actions file))]
      (is (seq (:trace result)) file)
      (is (empty? (keep :refusal (:trace result))) file)
      (is (empty? (b/violations result)) (str file " " (pr-str (b/violations result)))))))

(deftest f57-atomic-local-rejections
  (doseq [file (concat f57-files (io/read-witness "run10/index.edn"))
          mode [:frozen :materialized] protocol [:p1 :p1q]]
    (testing (str file " " mode " " protocol)
      (let [actions (r9/variant (r9/actions file) mode protocol)
            prefix (if (= :t24 (:t (peek actions))) (pop actions) actions)
            attached (b/execute prefix)
            before (:state attached)
            result (b/execute before [r9/release-child])
            after (:state result)
            obs (set (keys (get-in before [:worlds r9/child :obligations])))
            replies (:queue (m/wr after r9/child))
            cleanup (b/execute after (repeat (count obs) {:t :t36 :w r9/child}))]
        (is (empty? (keep :refusal (:trace attached))))
        (is (empty? (b/violations attached)) (pr-str (b/violations attached)))
        (is (seq obs))
        (is (every? (fn [[o ob]] (inv/attached-cut-pending? before r9/child o ob))
                    (get-in before [:worlds r9/child :obligations])))
        (is (empty? (:queue (m/wr before r9/child))))
        (is (empty? (keep :refusal (:trace result))))
        (is (empty? (b/violations result)) (pr-str (b/violations result)))
        (is (= (m/wr before b/v) (m/wr after b/v)))
        (is (= obs (set (map :cancelled replies))))
        (is (= (count obs) (count replies)))
        (is (every? #(= ::m/released (:value %)) replies))
        (is (apply < (get-in after [:worlds r9/child :seq]) (map :seq replies)))
        (is (= (get-in after [:clocks r9/child]) (:seq (peek replies))))
        (is (every? #(false? (inv/attached-cut-pending? after r9/child (key %) (val %)))
                    (get-in after [:worlds r9/child :obligations])))
        (is (empty? (keep :refusal (:trace cleanup))))
        (is (empty? (b/violations cleanup)) (pr-str (b/violations cleanup)))
        (is (empty? (get-in cleanup [:state :worlds r9/child :obligations])))
        (is (empty? (:queue (m/wr (:state cleanup) r9/child))))))))

(deftest attached-cut-exception-negative-controls
  (doseq [file f57-files]
    (let [s (:state (b/execute (r9/actions file)))
          ob (get-in s [:worlds r9/child :obligations [:o 1]])
          basis [:cuts r9/cut :basis b/w]
          cap-path (conj (m/cap-path s [:cap 1]) :published?)
          request {:start-for [:spin 1] :creditor-world r9/child :o [:o 1]}]
      (is (empty? (inv/l20 s)))
      (doseq [[label corrupt]
              [[:executable (assoc-in s [:worlds r9/child :admission] :open)]
               [:published (assoc-in s cap-path true)]
               [:no-capability (-> s (update :caps dissoc [:cap 1])
                                   (update-in [:durable :caps] dissoc [:cap 1]))]
               [:wrong-cut-phase (assoc-in s [:cuts r9/cut :phase] :released)]
               [:missing-basis (update-in s (conj basis :copy-evidence) dissoc [:o 1])]
               [:wrong-basis-phase (assoc-in s (into basis [:copy-evidence [:o 1] :phase]) :cancelling)]
               [:wrong-debtor (assoc-in s (into basis [:obligations [:o 1] :debtor]) [:entity b/v [:spin 3]])]
               [:not-inherited (assoc-in s [:worlds r9/child :runs b/r :status] :parked)]
               [:early-request (update-in s [:env :outside] conj {:w b/v :event request})]]]
        (testing (str file " " label)
          (is (false? (inv/attached-cut-pending? corrupt r9/child [:o 1] ob)))
          (is (seq (inv/l20 corrupt))))))))

(deftest local-rejection-footprint-negative-controls
  (doseq [file (io/read-witness "run10/index.edn")]
    (let [result (b/execute (r9/actions file))
          {:keys [before after] :as edge} (peek (:trace result))
          queue-path [:worlds r9/child :queue]
          clock-path [:clocks r9/child]]
      (is (= :t24 (get-in edge [:action :t])))
      (is (empty? (inv/edge-check edge)))
      (doseq [[label corrupt]
              [[:missing-member (update-in after queue-path pop)]
               [:wrong-reason (assoc-in after (into queue-path [0 :value]) :wrong)]
               [:wrong-member (assoc-in after (into queue-path [0 :cancelled]) [:o :forged])]
               [:wrong-sequence (assoc-in after (into queue-path [0 :seq]) 999)]
               [:wrong-clock (assoc-in after clock-path 999)]
               [:duplicate-member (update-in after queue-path conj (first (get-in after queue-path)))]]]
        (is (some #(= :TL6 (:id %)) (inv/edge-check (assoc edge :after corrupt))) (str file " " label)))
      ;; A released phase with the old event-free child is no longer exempt.
      (is (seq (inv/l20 (-> before (assoc-in [:cuts r9/cut :phase] :released)
                            (assoc-in [:worlds r9/child :admission] :open))))))))

(deftest tombstone-join-rejects-every-member
  (let [s (:state (b/execute (r9/actions "run9/F57-admitted-release.edn")))
        members {[:o 1] {:debtor [:spin 1]} [:o 2] {:debtor [:spin 1]}
                 [:o 3] {:debtor [:spin 2]}}
        result (m/enqueue s b/v {:join-bundle r9/child :debtors #{[:spin 1] [:spin 2]}
                                 :members members})
        replies (:queue (m/wr result r9/child))]
    (is (= (m/wr s b/v) (m/wr result b/v)))
    (is (= (set (keys members)) (set (map :cancelled replies))))
    (is (= (count members) (count replies)))
    (is (every? #(= ::m/released (:value %)) replies))
    (is (= result (m/enqueue result b/v {:join-bundle r9/child :members members})))
    (is (= s (m/enqueue s b/v {:cancelled :absent})))
    (is (= s (m/enqueue s b/v {:completion :absent})))))

(deftest f57-release-interleavings
  (doseq [[phase file] [[:pending "run9/F57-before-attach.edn"]
                        [:admitted "run9/F57-admitted-release.edn"]]]
    (let [actions (r9/actions file)
          initial (:state (b/execute (take-while #(not= :t26 (:t %)) actions)))
          alphabet (fn [s]
                     (concat
                      (case (get-in s [:cuts r9/cut :phase])
                        :captured [{:t :t23 :c r9/cut :v r9/child :k [:cap 1]} {:t :t25 :c r9/cut}]
                        :attached [r9/release-child {:t :t25 :c r9/cut}] [])
                      (case (:disposition (m/cap s b/cap))
                        :open [{:t :t26 :caller b/root :k b/cap :op :gone :kind :discard}]
                        :sealed [{:t :t27 :k b/cap :op :gone :steps []}]
                        :settling [{:t :t29 :op :gone}] [])
                      (for [w [b/v r9/child] :when (seq (:queue (m/wr s w)))] {:t :queued :w w})))
          report (b/bfs initial {:alphabet alphabet :seconds 3 :max-states 2000})]
      (b/report! (keyword (str "f57-" (name phase))) report)
      (is (empty? (:findings report)) (pr-str (:findings report)))
      (when (= :exhausted (:status report))
        (is (zero? (:pending report)))
        (is (zero? (:depth-cuts report)))))))

(defn -main [& [mode]]
  (require 'org.replikativ.spindel.lifetime.generative-check)
  (let [counts
        (binding [clojure.test/*report-counters* (ref clojure.test/*initial-report-counters*)]
          (clojure.test/test-vars
           (concat (remove #((set b/search-checks) (:name (meta %)))
                           (vals (ns-publics 'org.replikativ.spindel.lifetime.bfs-check)))
                   (vals (ns-publics 'org.replikativ.spindel.lifetime.generative-check))
                   (remove #(= 'join-interleavings (:name (meta %)))
                           (vals (ns-publics 'org.replikativ.spindel.lifetime.run9-check)))
                   (remove #(= 'f57-release-interleavings (:name (meta %)))
                           (vals (ns-publics 'org.replikativ.spindel.lifetime.run10-check)))))
          (println "LIFETIME UNIT-COUNTS" @clojure.test/*report-counters*)
          (when-not (= mode "regressions")
            (clojure.test/test-vars [#'r9/join-interleavings #'f57-release-interleavings])
            (doseq [check b/search-checks]
              (clojure.test/test-vars [(ns-resolve 'org.replikativ.spindel.lifetime.bfs-check check)])))
          (let [counts @clojure.test/*report-counters*]
            (io/write-report! "counts.edn" (pr-str counts))
            (println "LIFETIME TOTAL-COUNTS" counts)
            counts))]
    (shutdown-agents)
    (System/exit (if (zero? (+ (:fail counts) (:error counts))) 0 1))))
