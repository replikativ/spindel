(ns org.replikativ.spindel.lifetime.run11-check
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.lifetime.bfs-check :as b]
            [org.replikativ.spindel.lifetime.check-io :as io]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.run9-check :as r9]
            [org.replikativ.spindel.lifetime.run10-check :as r10]))

(def child [:spin 1])
(def child-run [child 1])
(def atom-id [:atom 0])

(deftest run11-artifacts
  (doseq [file (io/read-witness "run11/index.edn")]
    (testing file
      (let [actions (r9/actions file)
            result (b/execute actions) s (:state result)
            before (:before (peek (:trace result)))
            exits (filter #(= :run-exit (:event %)) (:events s))]
        (is (seq actions))
        (is (empty? (keep :refusal (:trace result))))
        (is (empty? (b/violations result)) (pr-str (b/violations result)))
        (is (= b/r (:owner (m/ent before b/w child))))
        (is (= b/root (:owner (m/run before b/w child-run))))
        ;; T2 records sources in creations for continuation-prefix adoption.
        (is (m/ent before b/w atom-id))
        (is (contains? (:creations (m/run before b/w child-run)) atom-id))
        (is (nil? (m/ent s b/w atom-id)))
        (is (not-any? #(= child (:spin %)) (vals (:runs (m/wr s b/w)))))
        (is (some #(and (= child-run (:r %)) (= :t10 (:t %))) exits))
        (if (= file "run11/stale-child.edn")
          (is (nil? (m/ent s b/w child)))
          (do (is (= 0 (:result (m/ent s b/w child))))
              (is (true? (:dirty? (m/ent s b/w child))))
              (is (nil? (:owner (m/ent s b/w child))))
              (is (m/idle? s b/w child))))))))

(deftest owner-release-also-covers-nonlexical-owned-state
  (let [actions (r9/actions "run11/V03-t11.edn")
        {:keys [before action]} (peek (:trace (b/execute actions)))
        ;; Ownership is authoritative even for a nonlexical resource whose
        ;; constructor has no creation entry in the owning run's CPS prefix.
        before (update-in before [:worlds b/w :runs child-run :creations] disj atom-id)
        after (m/step before action)]
    (is (empty? (inv/check before)))
    (is (empty? (inv/check after)))
    (is (nil? (m/ent after b/w atom-id)))
    (is (nil? (m/run after b/w child-run)))
    (is (empty? (inv/owner-release-errors before after)))))

(deftest owner-release-check-negative-controls
  (let [actions (r9/actions "run11/V03-t11.edn")
        {:keys [before after] :as edge} (peek (:trace (b/execute actions)))
        run-path [:worlds b/w :runs child-run]
        atom-path [:worlds b/w :entities atom-id]
        ;; Reinsert the old completed scope. A state-only predicate cannot
        ;; distinguish this from a legitimate pending foreign cleanup extent;
        ;; the owner-release transition check must still reject it.
        corrupt (-> after (assoc-in run-path (get-in before run-path))
                    (assoc-in atom-path (get-in before atom-path)))]
    (is (contains? (m/reasons corrupt b/w child) :extent))
    (is (not (m/execution-live? corrupt b/w child)))
    (is (some #(= :TL7 (:id %)) (inv/edge-check (assoc edge :after corrupt))))
    ;; A pin roots the graph; the independent rule-3 check still fails.
    (doseq [status [:completed :stale :running :parked]]
      (let [pinned (-> corrupt (update-in [:worlds b/w :pins] conj child)
                       (assoc-in (conj run-path :status) status))]
        (is (empty? (inv/l01 pinned)))
        (is (seq (inv/owner-release-errors before pinned)))
        (is (some #(= :TL7 (:id %)) (inv/edge-check (assoc edge :after pinned))))))))

(deftest t10-status-contract
  (let [s (:state (b/execute [b/invoke]))
        action {:t :t10 :w b/w :r b/r}
        result (m/attempt s action)]
    (is (= ::m/not-predecessor (get-in result [:refusal :error])))
    (is (= s (:state result)))
    (is (= (assoc s :events []) (:state (m/attempt s (assoc action :r [b/e 99])))))))

(def owned-child-bounds
  {:worlds 1 :world-ids 1 :spins 2 :signals 0 :atoms 1 :handles 1
   :generations 1 :invocations 1 :host-registrations 1 :scopes 0 :cuts 0
   :filters [:local] :invoke-modes [:callback]})

(defn owned-child-alphabet
  "Two structural sites: parent may create child; either may own the atom.
  Host invokes independently or in the parent run's scope. No GC or queue drain.
  One generation excludes successful T9; witnesses cover supersession variants."
  [s]
  (let [runs (:runs (m/wr s b/w))
        owners (cons b/root (keys runs))
        actions
        (concat
         [{:t :t13 :w b/w :scope b/root}]
         (for [owner (cons b/root (filter #(= b/e (first %)) (keys runs)))]
           {:t :t01 :w b/w :scope owner :e child :tok [:tok 0]})
         (for [e [b/e child] scope (if (= e child) (cons b/root (filter #(= b/e (first %)) (keys runs))) [b/root])
               :when (and (< (get-in s [:uses [:invoke b/w e]] 0) 1)
                          (< (get-in s [:generation-clock [b/w e]] 0) 1))]
           {:t :t04 :w b/w :e e :scope scope :mode :callback})
         (for [owner owners :when (zero? (get-in s [:uses [:source b/w :atom atom-id]] 0))]
           {:t :t02 :w b/w :scope owner :e atom-id :kind :atom :value 0})
         (for [[r _] runs t [:t07 :t10 :t11]] {:t t :w b/w :r r :value 0})
         (for [e [b/e child] :when (nil? (m/current s b/w e))]
           {:t :t09 :w b/w :e e}))]
    ;; Bounds restrict the alphabet only; all admitted successors, valid or not,
    ;; are checked and expanded by BFS. Refusals are retained.
    (filter #(m/within-bounds? (:state (m/attempt s %))) actions)))

(deftest owned-child-includes-v03
  (let [actions [{:t :t04 :w b/w :e b/e :scope b/root :mode :callback}
                 {:t :t01 :w b/w :scope b/r :e child :tok [:tok 0]}
                 {:t :t04 :w b/w :e child :scope b/root :mode :callback}
                 {:t :t02 :w b/w :scope child-run :e atom-id :kind :atom :value 0}
                 {:t :t07 :w b/w :r child-run :value 0}
                 {:t :t11 :w b/w :r b/r :value 0}]
        result (b/execute (m/init-state owned-child-bounds) actions)]
    (doseq [{:keys [before action after refusal]} (:trace result)]
      (is (some #{action} (owned-child-alphabet before)))
      (is (nil? refusal))
      (is (m/within-bounds? after)))
    (is (empty? (b/violations result)) (pr-str (b/violations result)))))

(deftest owned-child-exhaustion
  (let [report (b/bfs (m/init-state owned-child-bounds)
                      {:alphabet owned-child-alphabet :seconds 900 :max-states 100000})]
    (b/report! :owned-child report)
    (is (= :exhausted (:status report)))
    (is (zero? (:pending report)))
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
                           (vals (ns-publics 'org.replikativ.spindel.lifetime.run9-check)))
                   (remove #(= 'f57-release-interleavings (:name (meta %)))
                           (vals (ns-publics 'org.replikativ.spindel.lifetime.run10-check)))
                   (remove #(= 'owned-child-exhaustion (:name (meta %)))
                           (vals (ns-publics 'org.replikativ.spindel.lifetime.run11-check)))))
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
