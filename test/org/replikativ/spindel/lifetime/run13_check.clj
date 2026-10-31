(ns org.replikativ.spindel.lifetime.run13-check
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.lifetime.bfs-check :as b]
            [org.replikativ.spindel.lifetime.check-io :as io]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.rooted-liveness-test :as rooted]
            [org.replikativ.spindel.lifetime.run9-check :as r9]
            [org.replikativ.spindel.lifetime.run10-check :as r10]
            [org.replikativ.spindel.lifetime.run11-check :as r11]
            [org.replikativ.spindel.lifetime.run12-check :as r12]))

(def outer [:scope :id 0])
(def scope [:scope :id 1])
(def inner [:scope :id 2])
(def child r12/child)
(def cr r12/cr)
(def successor [b/e 2])
(def complete {:t :t07 :w b/w :r b/r :value :answer})
(def deliver {:t :queued :w b/w})
(def reenter {:t :t09 :w b/w :e b/e})
(def join-parent {:t :join :w b/w :x b/r})
(def completion [b/invoke r12/enter complete deliver])
(def supersession [b/invoke r12/enter reenter (assoc complete :r successor)])
(def nested
  [b/invoke {:t :t12 :w b/w :scope scope :parent b/r}
   {:t :t12 :w b/w :scope inner :parent scope}
   {:t :t04 :w b/w :scope inner :e child :mode :callback}
   (assoc r12/enter :r cr)])

(defn cuts [prefix]
  (into [(assoc b/following :systems #{:memory})]
        (concat (map #(if (:w %) (assoc % :w b/v) %) prefix)
                [(assoc r12/qcut :scope [:root b/v]) r12/merge-child r12/exit
                 (assoc r12/qcut :scope [:root b/v] :c [:cut 1])
                 {:t :t25 :c [:cut 1]} r12/merge-child])))

(def native-completion
  [b/invoke {:t :t05 :w b/w :r b/r :kind :external :debtor [:host :native]}
   {:t :t35 :th :host :op {:kind :resume :w b/w :o [:o 1]}}])
(def native-joined {:t :native-progress :n [:cancel [:o 1]] :state :joined})

(def cases
  {"completion-trailing-slice" (into completion [join-parent r12/exit join-parent])
   "superseded-executing-slice" (into supersession [join-parent r12/exit join-parent])
   "nested-cancel" (into nested [r12/cancel join-parent r12/exit join-parent])
   "nested-supersede" (into nested [reenter {:t :t10 :w b/w :r b/r} join-parent r12/exit join-parent])
   "nested-owner-release" (into [{:t :t12 :w b/w :scope outer :parent b/root}]
                                (concat (assoc nested 0 (assoc b/invoke :scope outer))
                                        [{:t :t13 :w b/w :scope outer} join-parent r12/exit join-parent]))
   "mixed-run-scope" [b/invoke {:t :t04 :w b/w :scope b/r :e child :mode :callback}
                      {:t :t12 :w b/w :scope scope :parent cr}
                      {:t :t04 :w b/w :scope scope :e [:spin 2] :mode :callback}
                      (assoc r12/enter :r [[:spin 2] 1]) r12/cancel]
   "native-only-completion" (into native-completion [complete deliver join-parent native-joined join-parent])
   "completion-cuts" (cuts completion)
   "supersession-cuts" (cuts (conj supersession deliver))})

(defn checked [actions]
  (let [result (b/execute actions)]
    (is (empty? (b/violations result)) (pr-str (b/violations result)))
    result))

(deftest run13-artifacts
  (doseq [file (io/read-witness "run13/index.edn")]
    (testing file
      (let [{:keys [actions]} (io/read-witness file)
            result (checked actions)]
        (is (seq actions))
        (is (= (get cases (subs file 6 (- (count file) 4))) actions))
        (is (= (if (.endsWith file "-cuts.edn") [::m/not-quiescent ::m/not-quiescent] [])
               (mapv :error (keep :refusal (:trace result)))))))))

(deftest logical-completion-before-physical-return
  (let [result (checked completion)
        completed (:after (nth (:trace result) 2))
        s (:state result) rr (m/run s b/w b/r)]
    (is (= :answer (:result (m/ent completed b/w b/e))))
    (is (= :completed (:status (m/run completed b/w b/r))))
    (is (= [:answer] (mapv :value (filter #(= :host-delivery (:event %)) (:events s)))))
    (is (nil? (m/ent s b/w b/e)))
    (is (= :unwinding (:status rr)))
    (is (= [b/r b/root b/w] (:anchor rr)))
    (is (= b/r (get-in s [:env :threads :host :run])))
    (is (= {:complete? false :busy [b/r]} (:observation (m/attempt s join-parent))))
    (let [after (:state (checked (conj completion r12/exit)))]
      (is (nil? (m/run after b/w b/r)))
      (is (= {:complete? true :busy []} (:observation (m/attempt after join-parent)))))))

(deftest distinct-generations-and-busy
  (let [s (:state (checked supersession))
        rr (m/run s b/w b/r)]
    (is (= :unwinding (:status rr)))
    (is (= :completed (:status (m/run s b/w successor))))
    (is (= successor (m/current s b/w b/e)))
    (is (= :answer (:result (m/ent s b/w b/e))))
    (is (m/busy? rr))
    (is (false? (m/quiescent? s b/w)))
    (is (= {:complete? false :busy [b/r]} (:observation (m/attempt s join-parent))))
    (is (nil? (m/run (:state (checked (conj supersession r12/exit))) b/w b/r)))))

(deftest nested-scope-retirement-anchors
  (doseq [name ["nested-cancel" "nested-supersede" "nested-owner-release"]]
    (testing name
      (let [actions (get cases name)
            result (checked actions)
            retirement (nth (:trace result) (- (count actions) 4))
            s (:after retirement) rr (m/run s b/w cr)
            expected (into [cr inner scope b/r]
                           (if (= name "nested-owner-release") [outer b/root b/w] [b/root b/w]))]
        (is (= :unwinding (:status rr)))
        (is (= expected (:anchor rr)))
        (is (nil? (get-in s [:worlds b/w :scopes scope])))
        (is (nil? (get-in s [:worlds b/w :scopes inner])))
        (is (= {:complete? false :busy [cr]} (:observation (m/attempt s join-parent))))
        (is (empty? (inv/l25 s)))
        (is (nil? (m/run (:state result) b/w cr)))
        (is (= {:complete? true :busy []} (:observation (peek (:trace result)))))))))

(deftest anchors-through-owned-runs-and-scopes
  (let [s (:state (checked (get cases "mixed-run-scope")))
        r [[:spin 2] 1]]
    (is (= [r scope cr b/r b/root b/w] (:anchor (m/run s b/w r))))
    (is (= {:complete? false :busy [r]} (:observation (m/attempt s join-parent))))))

(deftest no-scope-parent-even-when-already-closed
  (let [prefix (conj nested {:t :t13 :w b/w :scope scope})
        s (:state (checked (conj prefix r12/cancel)))]
    (is (= [cr inner scope b/r b/root b/w] (:anchor (m/run s b/w cr))))
    (is (nil? (get-in s [:worlds b/w :scopes scope])))
    (is (nil? (get-in s [:worlds b/w :scopes inner])))))

(deftest completion-native-and-slice-return-order
  (doseq [slice? [false true]
          :let [prefix (into native-completion (concat (when slice? [r12/enter]) [complete deliver]))
                s (:state (checked prefix))]]
    (is (= :unwinding (:status (m/run s b/w b/r))))
    (is (= {:complete? false :busy [b/r]} (:observation (m/attempt s join-parent))))
    (doseq [order (if slice? [[r12/exit native-joined] [native-joined r12/exit]] [[native-joined]])]
      (let [result (checked (into prefix order))
            after (:state result)]
        (when slice?
          (is (= :unwinding (:status (m/run (:after (nth (:trace result) (count prefix))) b/w b/r)))))
        (is (nil? (m/run after b/w b/r)))
        (is (= {:complete? true :busy []} (:observation (m/attempt after join-parent))))))))

(deftest retirement-l25-negative-controls
  (doseq [prefix [completion supersession (conj nested r12/cancel)]]
    (let [s (:state (checked prefix))
          r (if (= prefix (conj nested r12/cancel)) cr b/r)]
      (doseq [bad [(assoc-in s [:worlds b/w :runs r :owner] b/root)
                   (assoc-in s [:worlds b/w :scopes [:scope :id 99]] {:status :closed :parent r})
                   (assoc-in s [:worlds b/w :runs r :retired?] false)
                   (assoc-in s [:worlds b/w :runs r :anchor] [r])]]
        (is (seq (inv/l25 bad)))))))

(def owned-child-bounds (assoc r12/owned-child-bounds :scopes 1))

(defn owned-child-alphabet [s]
  (distinct
   (concat
    (r12/owned-child-alphabet s)
    (filter #(m/within-bounds? (:state (m/attempt s %)))
            (concat
             (when-not (get-in s [:worlds b/w :scopes scope])
               (for [[r rr] (:runs (m/wr s b/w)) :when (not= :unwinding (:status rr))]
                 {:t :t12 :w b/w :scope scope :parent r}))
             (when (get-in s [:worlds b/w :scopes scope])
               [{:t :t13 :w b/w :scope scope}]))))))

(deftest owned-child-includes-f59
  (let [actions (assoc (:actions (get r12/findings "F59-child-scope"))
                       0 (assoc b/invoke :scope b/root)
                       1 (assoc (second (:actions (get r12/findings "F59-child-scope"))) :scope scope)
                       3 (assoc r12/cancel :value 0))
        result (b/execute (m/init-state owned-child-bounds) actions)]
    (doseq [{:keys [before action after refusal]} (:trace result)]
      (is (some #{action} (owned-child-alphabet before)))
      (is (nil? refusal))
      (is (m/within-bounds? after)))
    (is (empty? (b/violations result)))))

(deftest owned-child-exhaustion
  (let [report (b/bfs (m/init-state owned-child-bounds)
                      {:alphabet owned-child-alphabet :seconds 1800 :max-states 300000
                       :compact-keys? true})]
    (b/report! :owned-child report)
    (is (= :exhausted (:status report)))
    (is (zero? (:pending report)))
    (is (zero? (:depth-cuts report)))
    (is (empty? (:findings report)) (pr-str (:findings report)))))

(deftest rooted-foreign-extent-gc-interleavings
  (let [w rooted/w v rooted/v
        initial (reduce m/step (m/init-state)
                        (subvec (rooted/foreign-owned-ancestor-actions) 0 14))
        actions [{:t :unsubscribe :w w :o [:o 0]}
                 {:t :unsubscribe :w v :o [:o 2]}
                 {:t :t16 :tok :hp} {:t :t16 :tok :ha}
                 {:t :t17 :w w :e :p :tok :hp} {:t :t17 :w w :e :a :tok :ha}
                 {:t :t18 :w w} {:t :t18 :w v}]
        report (b/bfs initial {:alphabet (constantly actions) :seconds 45 :max-states 10000})]
    (b/report! :rooted-foreign-extent-gc report)
    (is (= :exhausted (:status report)))
    (is (zero? (:pending report)))
    (is (zero? (:depth-cuts report)))
    (is (empty? (:findings report)) (pr-str (:findings report)))))

(defn regressions! []
  (require 'org.replikativ.spindel.lifetime.generative-check
           'org.replikativ.spindel.lifetime.transition-catalog-coverage-test
           'org.replikativ.spindel.lifetime.custody-model-test
           'org.replikativ.spindel.lifetime.idle-retirement-test)
  (doseq [[namespace excluded]
          [['org.replikativ.spindel.lifetime.bfs-check (set b/search-checks)]
           ['org.replikativ.spindel.lifetime.generative-check #{}]
           ['org.replikativ.spindel.lifetime.transition-catalog-coverage-test #{}]
           ['org.replikativ.spindel.lifetime.custody-model-test #{}]
           ['org.replikativ.spindel.lifetime.idle-retirement-test #{}]
           ['org.replikativ.spindel.lifetime.run9-check #{'join-interleavings}]
           ['org.replikativ.spindel.lifetime.run10-check #{'f57-release-interleavings}]
           ['org.replikativ.spindel.lifetime.run11-check #{'owned-child-exhaustion}]
           ['org.replikativ.spindel.lifetime.run12-check #{'owned-child-exhaustion}]
           ['org.replikativ.spindel.lifetime.run13-check #{'owned-child-exhaustion}]]]
    (clojure.test/test-vars (remove #(excluded (:name (meta %))) (vals (ns-publics namespace))))))

(defn -main [& [mode]]
  (let [counts
        (binding [clojure.test/*report-counters* (ref clojure.test/*initial-report-counters*)]
          (when-not (= mode "searches")
            (regressions!)
            (println "LIFETIME UNIT-COUNTS" @clojure.test/*report-counters*))
          (when-not (= mode "regressions")
            (clojure.test/test-vars [#'r9/join-interleavings #'r10/f57-release-interleavings])
            (doseq [check (remove #{'reduced-complete-search 'broad-searches} b/search-checks)]
              (clojure.test/test-vars [(ns-resolve 'org.replikativ.spindel.lifetime.bfs-check check)]))
            (clojure.test/test-vars [#'b/reduced-complete-search #'owned-child-exhaustion #'b/broad-searches]))
          (let [counts @clojure.test/*report-counters*]
            (io/write-report! (str (or mode "all") "-counts.edn") (pr-str counts))
            (println "LIFETIME RUN13 COUNTS" counts)
            counts))]
    (shutdown-agents)
    (System/exit (if (zero? (+ (:fail counts) (:error counts))) 0 1))))
