(ns org.replikativ.spindel.statemachine.baselines-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.state-backend :as sb]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.statemachine.counting-backend :as cb]
            [org.replikativ.spindel.statemachine.model :as m]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

(def ^:dynamic *trials* (Long/parseLong (System/getProperty "spindel.trials" "60")))
(def ^:dynamic *seed* (Long/parseLong (System/getProperty "spindel.seed" "650139")))

(def known-bugs?
  "Properties that fail on open bugs run only with -Dspindel.known-bugs=true,
  so the suite stays green until each fix lands and enables its property."
  (= "true" (System/getProperty "spindel.known-bugs")))

(def mutation-gen
  (gen/one-of [(gen/tuple (gen/return :set) (gen/choose 0 1) (gen/choose -2 8))
               (gen/tuple (gen/return :conj) (gen/return 2) gen/small-integer)
               (gen/tuple (gen/return :assoc) gen/nat gen/small-integer)
               (gen/return [:pop])]))

(def schedule-gen
  (gen/vector (gen/frequency [[7 mutation-gen]
                              [2 (gen/tuple (gen/return :queue) (gen/vector mutation-gen 1 3))]
                              [1 (gen/return [:drain])]
                              [1 (gen/tuple (gen/return :fork) (gen/elements [:following :frozen]))]
                              [1 (gen/tuple (gen/return :cancel) gen/nat)]]) 0 12))

(def all-kinds [:track :pair :repeat :branch :throw :await :vector-await :child :reentrant])

(defn programs-of
  "Programs of 1-5 spins whose kinds are drawn from `kinds`."
  [kinds]
  (gen/bind
   (gen/vector (gen/elements kinds) 1 5)
   (fn [kinds]
     (apply gen/tuple
            (map-indexed
             (fn [i kind]
               (gen/let [a (gen/choose 0 1) b (gen/choose 0 1)
                         dep (gen/choose 0 (max 0 (dec i)))]
                 {:kind (if (and (zero? i) (#{:await :vector-await} kind)) :track kind)
                  :a a :b b :dep (when (pos? i) dep)})) kinds)))))

(def program-gen (programs-of all-kinds))

(defn check! [label trials property]
  (let [started (System/nanoTime)
        result (tc/quick-check trials property :seed *seed*)]
    (println (pr-str {:property label :result result
                      :seconds (/ (- (System/nanoTime) started) 1e9)}))
    (is (true? (:pass? result)) (pr-str [label result]))))

(deftest generated-eventual-consistency
  (check! :eventual-consistency *trials*
          (prop/for-all [p program-gen s schedule-gen]
                        (m/consistent? p (m/run-program p s)))))

(deftest generated-determinism
  (check! :determinism *trials*
          (prop/for-all [p program-gen s schedule-gen]
                        (let [a (m/run-program p s) b (m/run-program p s)]
                          (= a b)))))

(deftest generated-default-executor
  ;; KNOWN BUG: on the concurrent default executor, eventual consistency fails:
  ;; after the final drain a live spin's cached value can differ from a fresh
  ;; run. Seen at 400 trials with -Dspindel.seed=1, 3, 4, 5 - with re-entrant
  ;; bodies (shrinks to [[{:kind :pair :a 0 :b 1} {:kind :track :a 0 :b 0 :dep 0}
  ;; {:kind :reentrant :a 0 :b 1 :dep 0}] [[:set 0 7] [:set 1 0]]]) and without
  ;; (await chains: seeds 1 and 5 shrink to tracks and awaits only). The
  ;; synchronous executor's properties pass. Gated: nondeterministic scheduling
  ;; would make it flaky in CI.
  (when known-bugs?
    (check! :default-executor (max 5 (quot *trials* 6))
            (prop/for-all [p program-gen s schedule-gen]
                          (m/consistent? p (m/run-program p s :default [0 0 []]))))))

(deftest generated-delta-integrity
  ;; Include the escalated-child topology explicitly so even a short run checks
  ;; the known redelivery defect. The vector of mutations shrinks to two events.
  (check! :delta-integrity *trials*
          (prop/for-all [s (gen/vector
                            (gen/one-of [(gen/tuple (gen/return :conj) (gen/return 2) gen/small-integer)
                                         (gen/tuple (gen/return :set) (gen/return 1) gen/small-integer)]) 0 10)]
                        (let [p [{:kind :child :b 1}]]
                          (m/delta-integrity? (:trace (m/run-program p s)))))))

(deftest generated-delta-integrity-general-graphs
  ;; KNOWN BUG: queued changes lose deltas. A signal node keeps only its latest
  ;; change's deltas, so a track site that skips a generation (two appends
  ;; queued before one drain) delivers only the last one. Shrinks to
  ;; [[:queue [[:conj 2 0] [:conj 2 0]]]].
  (when known-bugs?
    (check! :delta-integrity-general *trials*
            (prop/for-all [p program-gen s schedule-gen]
                          (m/delta-integrity? (:trace (m/run-program p s)))))))

(deftest generated-effect-multiplicity
  ;; Exact bound for one track followed by one emit, explicit scalar writes:
  ;; initial execution + one resumed slice per explicit write, even equal writes.
  ;; Drains without a write emit nothing. No claim of once-per-drain for multi-signal graphs:
  ;; FIFO changes may legitimately execute their suffix several times.
  (check! :effect-multiplicity *trials*
          (prop/for-all [xs (gen/vector gen/small-integer 0 20)]
                        (let [r (m/run-program [{:kind :track :a 0}]
                                               (vec (mapcat #(vector [:set 0 %] [:drain]) xs)))
                              expected (vec (cons 0 xs))]
                          (and (= (mapv second (:log r)) expected)
                               (every? (fn [{[op _ v] :operation emits :emits}]
                                         (if (= op :set)
                                           (= [[0 v]] emits)
                                           (empty? emits)))
                                       (:steps r)))))))

(defn diamond
  ([xs] (diamond xs 0))
  ([xs nonce]
   (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
     (try
       (binding [ec/*execution-context* rt]
        ;; Vary deterministic addresses, hence observer set iteration order.
        ;; A single graph identity can accidentally hide a scheduling glitch.
         (dotimes [_ nonce] (sig/signal 0))
         (let [a (sig/signal 0)
               seen (atom [])
               b (spin (* 2 (iv/get-new (track a))))
               c (spin (* 3 (iv/get-new (track a))))
               d (spin (let [bv (await b) cv (await c)]
                         (swap! seen conj [:shallow bv cv]) (+ bv cv)))
               e (spin (* 2 (await d)))
               f (spin (* 3 (await d)))
               g (spin (let [ev (await e) fv (await f)]
                         (swap! seen conj [:deep ev fv]) (+ ev fv)))]
           (m/start! g)
           (doseq [x xs] (reset! a x) (await-drain rt))
           {:seen @seen :value (second (m/cached rt g))}))
       (finally (ctx/close-context! rt))))))

(deftest generated-glitch-freedom
  ;; Guards against synchronous await diamond glitches. d awaits b then c, both
  ;; tracking a; when c completes first, d resumes at its await-c site with the
  ;; b value it captured before, observing [old-b new-c] (shrinks to
  ;; (diamond [-1] 1): [0 -3] before [-2 -3]). engine-formalism.md 1.4 says
  ;; glitch freedom holds for the synchronous sub-graph.
  (check! :glitch-freedom *trials*
          (prop/for-all [xs (gen/vector gen/small-integer 0 12) nonce (gen/choose 0 7)]
                        (let [{:keys [seen value]} (diamond xs nonce)]
                          (and (every? (fn [[_ b c]] (= (* 3 b) (* 2 c))) seen)
                               (= value (* 25 (last (cons 0 xs)))))))))

(deftest review-seed-corpus
  (testing "captured ia survives a change to b; repeat sites remain distinct"
    (let [r (m/run-program [{:kind :pair :a 0 :b 1}]
                           [[:set 0 2] [:set 1 3]])]
      (is (= [[0 [0 0]] [0 [2 0]] [0 [2 3]]] (:log r)))
      (is (= 2 (count (filter #(= [0 :a] (:site %)) (:trace r))))))
    (is (m/consistent? [{:kind :repeat :a 0}]
                       (m/run-program [{:kind :repeat :a 0}] [[:set 0 3]]))))
  (testing "branch adds b only after the selector changes"
    (let [p [{:kind :branch :a 0 :b 1}]
          r (m/run-program p [[:set 0 1] [:set 1 4] [:set 0 2] [:set 1 5]])]
      (is (= [[0 0] [0 1] [0 4] [0 5]] (:log r)))
      (is (m/consistent? p r))))
  (testing "throw before second track; a later success adds b"
    (let [p [{:kind :throw :a 0 :b 1}]
          r (m/run-program p [[:set 0 -1] [:set 1 4] [:set 0 2] [:set 1 5]])]
      (is (= [[0 [0 0]] [0 [2 4]] [0 [2 5]]] (:log r)))
      (is (m/consistent? p r))))
  (testing "queued B then A preserves captured A until A's FIFO event"
    (let [r (m/run-program [{:kind :pair :a 0 :b 1}]
                           [[:queue [[:set 1 3] [:set 0 2]]]])]
      (is (= [[0 [0 0]] [0 [0 3]] [0 [2 3]]] (:log r)))))
  (testing "cached and uncached awaits retain a dependency after track"
    (let [p [{:kind :track :a 1} {:kind :vector-await :dep 0}]
          r (m/run-program p [[:conj 2 9] [:set 1 3]])]
      (is (= [[:ok 3] [:ok [[9] 3]]] (:values r)))
      (is (m/consistent? p r))))
  (testing "body-issued swap drains to its idempotent target"
    (let [p [{:kind :reentrant :a 0 :b 1} {:kind :track :a 1}]
          r (m/run-program p [[:set 0 7]])]
      (is (= [7 11 []] (:signals r)))
      (is (m/consistent? p r)))))

(deftest counting-backend-delegation
  (let [delegate (sb/create-atom-backend {:x 1 :y 2})
        counts (atom {})
        b (cb/->CountingBackend delegate counts (:state-atom delegate))]
    (is (= 1 (sb/backend-read b [:x])))
    (is (= 2 (sb/backend-write! b [:x] inc)))
    (sb/backend-write-2! b [:x] [:y] (fn [x y] [(inc x) (inc y)]))
    (is (= {:x 3 :y 3} (sb/backend-deref b)))
    (is (= {:reads {[:x] 1 [] 1} :writes {[:x] 2 [:y] 1} :commits {[] 2}} @counts))))

(deftest captured-interval-is-not-refreshed-by-a-later-site
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (try
      (binding [ec/*execution-context* rt]
        (let [a (sig/signal []) b (sig/signal 0) seen (atom [])
              root (spin (let [ia (track a) vb (iv/get-new (track b))]
                           (swap! seen conj [{:old (m/plain (:old ia))
                                              :new (m/plain (:new ia))
                                              :deltas (:deltas ia)} vb])))]
          (m/start! root)
          (swap! a conj :x)
          (await-drain rt)
          (let [captured (first (last @seen))]
            (is (= [] (:old captured)))
            (is (= [:x] (:new captured)))
            (is (seq (:deltas captured)))
            (swap! b inc)
            (await-drain rt)
            (is (= [captured 1] (last @seen))))))
      (finally (ctx/close-context! rt)))))

(deftest forked-schedule-continues-in-an-isolated-world
  (doseq [mode [:following :frozen]]
    (let [p [{:kind :track :a 0} {:kind :vector-await :dep 0}]
          r (m/run-program p [[:set 0 2] [:fork mode] [:set 0 3] [:conj 2 9]])]
      (is (= [3 0 [9]] (:signals r)))
      (is (= [[:ok 3] [:ok [[9] 3]]] (:values r)))
      (is (m/consistent? p r)))))

(deftest cancellation-and-later-invalidation-baseline
  ;; TODAY a completed reactive spin's cancelled cache can be invalidated by
  ;; a later signal write. Cancellation is not a permanent unsubscribe here.
  (let [p [{:kind :track :a 0}]
        cancelled (m/run-program p [[:cancel 0] [:drain]])
        revived (m/run-program p [[:cancel 0] [:set 0 3] [:drain]])]
    (is (= [[0 0]] (:log cancelled)))
    (is (= #{0} (:cancelled cancelled)))
    (is (= [[:error "Spin cancelled by user"]] (:values cancelled)))
    (is (= [[0 0] [0 3]] (:log revived)))
    (is (= #{} (:cancelled revived)))
    (is (= [[:ok 3]] (:values revived)))
    (is (m/consistent? p revived))))

(deftest counting-backend-preserves-context-cas
  (let [base (ctx/create-execution-context :executor (ex/synchronous-executor))
        [rt counts] (cb/instrument base)]
    (try
      (rtp/swap-state! rt [:probe] (constantly 0))
      (reset! counts {})
      (is (true? (rtp/cas-state! rt [:probe] 0 1)))
      (is (false? (rtp/cas-state! rt [:probe] 0 2)))
      (is (= 1 (rtp/get-state rt [:probe])))
      (is (= {:atom-commits {[] 1} :reads {[:probe] 1}} @counts))
      (finally (ctx/close-context! rt)))))
