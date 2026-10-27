(ns org.replikativ.spindel.lifetime.run9-check
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.lifetime.bfs-check :as b]
            [org.replikativ.spindel.lifetime.check-io :as io]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.model :as m]))

(def child [:w 2])
(def cut [:cut 0])
(def release-child {:t :t24 :c cut})
(defn actions [file] (:actions (io/read-witness file)))

(deftest run9-artifacts
  (doseq [file (io/read-witness "run9/index.edn")]
    (let [{:keys [actions finding target]} (io/read-witness file)
          result (b/execute actions)]
      (is (seq actions) file)
      (is (empty? (keep :refusal (:trace result))) file)
      (when finding
        (is (some #(= target (:id %)) (b/first-failure actions)) file)
        (is (= actions (b/shortest-subsequence actions target)) file))
      ;; Keep the normative assertion red for a specification counterexample.
      (is (empty? (b/violations result)) (str file " " (pr-str (b/violations result)))))))

(defn variant [trace mode protocol]
  (vec (mapcat (fn [a]
                 (cond
                   (= :t20q (:t a)) (if (= :p1 protocol)
                                      [(assoc a :t :t20 :mode mode) {:t :t21 :c (:c a)}]
                                      [(assoc a :mode mode)])
                   (= :t23 (:t a)) [(assoc a :mode mode)]
                   :else [a])) trace)))

(deftest f55-f56-variants
  (doseq [file ["run8/F55.edn" "run8/F55-after-attach.edn"
                "run8/F55-released-debtor.edn" "run8/F56.edn"
                "run9/F57-after-attach.edn" "run9/F57-admitted-release.edn"
                "run9/F57-admitted-after-attach.edn"]
          mode [:frozen :materialized] protocol [:p1q :p1]]
    (testing (str file " " mode " " protocol)
      (let [trace (variant (actions file) mode protocol)
            ;; F55's final T36 now has no request to process before T24.
            trace (if (= file "run8/F55.edn") (pop trace) trace)
            attached (b/execute trace)
            state (:state attached)
            ob (get-in state [:worlds child :obligations [:o 1]])
            released (b/execute (concat trace [release-child]))
            after (:state released)
            replies (loop [result {:state after :trace []} worlds [b/v child]]
                      (if-let [world (first worlds)]
                        (if (seq (:queue (m/wr (:state result) world)))
                          (let [step (b/execute (:state result) [{:t :queued :w world}])]
                            (recur (update step :trace #(into (:trace result) %)) worlds))
                          (recur result (rest worlds))) result))
            rolled-back (b/execute state [{:t :t25 :c cut}])]
        (is (empty? (keep :refusal (:trace attached))))
        (is (= :fenced (:admission (m/wr state child))))
        (is (= [:pending-start] (inv/obligation-phases state child [:o 1] ob)))
        (is (not-any? #(or (= child (:join-bundle %)) (= child (:creditor-world %)))
                      (inv/queued-events state b/v)))
        (is (empty? (b/violations attached)) (pr-str (b/violations attached)))
        (is (empty? (keep :refusal (:trace released))))
        (is (= :open (:admission (m/wr after child))))
        (is (every? :published? (vals (m/caps-of after child))))
        (is (empty? (inv/check after)) (pr-str (inv/check after)))
        (is (empty? (inv/check-trace (:trace released))) (pr-str (inv/check-trace (:trace released))))
        (is (empty? (keep :refusal (:trace replies))))
        (is (empty? (b/violations replies)) (pr-str (b/violations replies)))
        (is (every? #(= :open (:admission (m/wr (:before %) child))) (:trace replies)))
        (is (empty? (b/violations rolled-back)) (pr-str (b/violations rolled-back)))
        (is (= (m/wr state b/v) (m/wr (:state rolled-back) b/v)))
        (is (nil? (m/wr (:state rolled-back) child)))))))

(deftest t23-and-t24-exact-footprints
  (doseq [file ["run9/join-at-release.edn" "run9/start-at-release.edn"]]
    (let [trace (:trace (b/execute (actions file)))
          attach (first (filter #(= :t23 (get-in % [:action :t])) trace))
          release (first (filter #(= :t24 (get-in % [:action :t])) trace))
          {before :before after :after} attach
          ob (get-in after [:worlds child :obligations [:o 1]])
          request (first (filter #(or (= child (:join-bundle %)) (= child (:creditor-world %)))
                                 (inv/queued-events (:after release) b/v)))]
      (is (= (m/wr before b/v) (m/wr after b/v)))
      (is (= (:clocks before) (:clocks after)))
      (is (empty? (inv/edge-check attach)))
      (is (= [:pending-start] (inv/obligation-phases after child [:o 1] ob)))
      (is (seq (inv/l10 (assoc-in after [:cuts cut :phase] :released))))
      (is (seq (inv/l10 (assoc-in after [:worlds b/v :fdeps] #{[:bundle child #{[:spin 1]}]}))))
      (is request)
      (is (empty? (inv/edge-check release)))
      ;; A request one transaction early, a forged request at release, and a
      ;; foreign dependency write all remain footprint violations.
      (doseq [[edge corrupt]
              [[attach (update-in after [:worlds b/v :queue] conj request)]
               [release (update-in (:after release) [:worlds b/v :queue] conj {:start-for :forged})]
               [release (update-in (:after release) [:worlds b/v :fdeps] conj [:bundle child #{[:spin 1]}])]]]
        (is (some #(= :TL6 (:id %)) (inv/edge-check (assoc edge :after corrupt)))))
      (let [corrupt (update-in after [:worlds child :queue] conj {:cancelled [:o 1]})]
        (is (seq (inv/l22 corrupt)))))))

(deftest t25-never-issues-requests
  (let [result (b/execute (actions "run9/rollback-two-members.edn"))
        {:keys [before after] :as edge} (last (:trace result))]
    (is (empty? (b/violations result)))
    (is (= (m/wr before b/v) (m/wr after b/v)))
    (is (= (:clocks before) (:clocks after)))
    (is (= (get-in before [:env :outside]) (get-in after [:env :outside])))
    (is (nil? (m/wr after child)))
    (is (empty? (m/caps-of after child)))
    (is (some #(= :TL6 (:id %))
              (inv/edge-check (update edge :after update-in [:worlds b/v :queue] conj
                                      {:join-bundle child :members {}}))))))

(deftest requests-to-another-fenced-world
  (let [prefix (actions "run8/F56.edn")
        fence {:t :t20 :c [:cut 1] :scope [:root b/v] :coordinator :other
               :participants {:worlds #{b/v} :components #{[b/v :sci-c]} :systems #{:c}}}
        result (b/execute (concat prefix [fence release-child]))
        held (get-in result [:state :env :outside])]
    (is (empty? (keep :refusal (:trace result))))
    (is (empty? (b/violations result)) (pr-str (b/violations result)))
    (is (= 1 (count held)))
    (is (= child (get-in (first held) [:event :creditor-world])))
    (is (= b/v (:w (first held))))))

(deftest join-interleavings
  ;; The run-8 suffix alphabet and limits, retained as a packaged check.
  (let [initial (:state (b/execute (take 6 (actions "run8/cancel-after-capture.edn"))))
        alphabet (fn [s]
                   (concat
                    (when (m/run s b/v [[:spin 1] 1]) [{:t :t11 :w b/v :r [[:spin 1] 1]}])
                    (case (get-in s [:cuts cut :phase])
                      :captured [{:t :t23 :c cut :v child :k [:cap 1]} {:t :t25 :c cut}]
                      :attached [release-child {:t :t25 :c cut}] [])
                    (for [world [b/v child] :when (seq (:queue (m/wr s world)))]
                      {:t :queued :w world})))
        report (b/bfs initial {:alphabet alphabet :seconds 3 :max-states 2000})]
    (b/report! :join-interleavings report)
    (is (= :exhausted (:status report)))
    (is (zero? (:depth-cuts report)))
    (is (empty? (:findings report)) (pr-str (:findings report)))))

(defn -main [& [mode]]
  (require 'org.replikativ.spindel.lifetime.generative-check)
  (let [counts
        (binding [clojure.test/*report-counters* (ref clojure.test/*initial-report-counters*)]
          (clojure.test/test-vars
           (concat (remove #((set b/search-checks) (:name (meta %)))
                           (vals (ns-publics 'org.replikativ.spindel.lifetime.bfs-check)))
                   (vals (ns-publics 'org.replikativ.spindel.lifetime.generative-check))
                   (remove #(= 'join-interleavings (:name (meta %)))
                           (vals (ns-publics 'org.replikativ.spindel.lifetime.run9-check)))))
          (println "LIFETIME UNIT-COUNTS" @clojure.test/*report-counters*)
          (when-not (= mode "regressions")
            (clojure.test/test-vars [#'join-interleavings])
            (doseq [check b/search-checks]
              (clojure.test/test-vars [(ns-resolve 'org.replikativ.spindel.lifetime.bfs-check check)])))
          (let [counts @clojure.test/*report-counters*]
            (io/write-report! "counts.edn" (pr-str counts))
            (println "LIFETIME TOTAL-COUNTS" counts)
            counts))]
    (shutdown-agents)
    (System/exit (if (zero? (+ (:fail counts) (:error counts))) 0 1))))
