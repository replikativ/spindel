(ns org.replikativ.spindel.engine.trace-addressing-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.addressing :as address]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.owned :as owned #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]))

(def site {:file "trace-addressing-test" :line 1 :column 1})

(defn- successor [head]
  (keyword (str "spin-" (address/chain-hash site head))))

(defn- next! []
  (address/next-address! (ec/current-execution-context) "spin" site))

(defn- observe! [rt spin results]
  (binding [ec/*execution-context* rt]
    (owned/observe! rt spin #(swap! results conj %) #(swap! results conj [:error %]))))

(deftest both-engines-preserve-the-root-hash-chain
  (let [legacy (context/create-execution-context)
        native (owned/runtime)]
    (try
      (doseq [rt [legacy native]]
        (binding [ec/*execution-context* rt]
          (let [first-id (next!) second-id (next!)]
            (is (= (successor nil) first-id))
            (is (= (successor first-id) second-id))
            (is (not= first-id second-id)))))
      (finally (context/stop-context! legacy)))))

(deftest legacy-body-seeding-still-isolates-the-parent-cursor
  (let [rt (context/create-execution-context)]
    (try
      (binding [ec/*execution-context* rt ec/*spin-id* :parent]
        (address/seed-body-chain-head! rt :parent)
        (let [first-id (next!)]
          (is (= (successor (address/body-start-chain-head :parent)) first-id))
          (binding [ec/*spin-id* :child]
            (address/seed-body-chain-head! rt :child)
            (is (= (successor (address/body-start-chain-head :child)) (next!))))
          (is (= (successor first-id) (next!)))))
      (finally (context/stop-context! rt)))))

(deftest native-reactive-resumes-restore-each-sites-cursor
  (let [rt (owned/runtime {:audit? true})
        early (owned/signal rt :early 0) late (owned/signal rt :late 0)
        results (atom [])
        spin (owned/cspin rt :parent
                          (let [a (next!)]
                            (owned/track early)
                            (let [b (next!)]
                              (owned/track late)
                              [a b (next!)])))]
    (observe! rt spin results)
    (owned/set-signal! rt late 1)
    (owned/set-signal! rt early 1)
    (let [a (successor (address/body-start-chain-head :parent))
          b (successor a) expected [a b (successor b)]]
      (is (= [expected expected expected] @results)))
    (verify-boundaries! rt)))

(deftest native-child-entry-and-inline-await-do-not-reset-the-parent
  (doseq [cached? [false true]]
    (let [rt (owned/runtime {:audit? true}) results (atom [])
          child (owned/cspin rt :child (next!))
          parent (owned/cspin rt :parent
                              (let [a (next!) child-value (owned/await child)]
                                [a child-value (next!)]))]
      (when cached? (observe! rt child (atom [])))
      (observe! rt parent results)
      (let [a (successor (address/body-start-chain-head :parent))]
        (is (= [[a (successor (address/body-start-chain-head :child)) (successor a)]] @results)))
      (verify-boundaries! rt))))

(deftest native-decorated-and-explicit-foreign-world-cursors-have-distinct-authority
  (let [rt (owned/runtime {:audit? true}) other (owned/runtime {:audit? true})
        results (atom [])
        spin (owned/cspin rt :parent
                          (let [a (address/next-address! (assoc ec/*execution-context* :bindings {:key :lexical}) "spin" site)
                                foreign (address/next-address! other "spin" site)]
                            [a foreign (next!)]))]
    (observe! rt spin results)
    (let [a (successor (address/body-start-chain-head :parent))]
      (is (= [[a (successor nil) (successor a)]] @results)))
    (is (= (successor nil) (address/next-address! rt "spin" site)))
    (is (= (successor (successor nil)) (address/next-address! other "spin" site)))
    (verify-boundaries! rt)
    (verify-boundaries! other)))

(deftest parked-forks-copy-root-and-suspended-run-cursors-by-value
  (let [rt (owned/runtime {:audit? true}) results (atom []) seen (atom [])
        gate (owned/ticket :body)
        root-head (address/next-address! rt "spin" site)
        spin (owned/cspin rt :parent
                          (let [a (next!)]
                            (owned/park gate)
                            (swap! seen conj [(:world ec/*execution-context*) a (next!)])))]
    (observe! rt spin results)
    (let [child (owned/fork-parked! rt [:w 1])
          expected-first (successor (address/body-start-chain-head :parent))]
      (is (= (successor root-head) (address/next-address! rt "spin" site)))
      (is (= (successor root-head) (address/next-address! child "spin" site)))
      (owned/resume-ticket! child (owned/pending-ticket child gate) :ready)
      (owned/resume-ticket! rt (owned/pending-ticket rt gate) :ready)
      (is (= [[[:w 1] expected-first (successor expected-first)]
              [owned/w expected-first (successor expected-first)]] @seen)))
    (verify-boundaries! rt)))

(deftest protected-cleanup-cannot-consume-an-ordinary-or-root-cursor
  (let [rt (owned/runtime {:audit? true :cps-exit? true})
        callback (atom nil) refused (atom []) results (atom [])
        spin (owned/cspin rt :parent
                          (next!)
                          (try (owned/park (owned/ticket :body))
                               (finally
                                 (try (next!)
                                      (catch #?(:clj Exception :cljs :default) error
                                        (swap! refused conj (:error (ex-data error)))))
                                 (owned/await-finalization (fn [resolve _] (reset! callback resolve)))
                                 (try (next!)
                                      (catch #?(:clj Exception :cljs :default) error
                                        (swap! refused conj (:error (ex-data error))))))))]
    (observe! rt spin results)
    (owned/cancel-spin! rt spin)
    (is (= [:cleanup-only] @refused))
    (is (fn? @callback))
    (when-let [resume @callback] (resume :ready))
    (is (= [:cleanup-only :cleanup-only] @refused))
    (is (= (successor nil) (address/next-address! rt "spin" site)))
    (is (owned/join-ready? rt [:parent 1]))
    (verify-boundaries! rt)))

#?(:clj
   (deftest concurrent-native-root-construction-does-not-reuse-addresses
     (let [rt (owned/runtime)
           jobs (doall (repeatedly 8 #(future (vec (repeatedly 30 (fn [] (address/next-address! rt "spin" site)))))))
           actual (mapcat deref jobs)
           expected (take 240 (rest (iterate successor nil)))]
       (is (= 240 (count (set actual))))
       (is (= (set expected) (set actual))))))

(deftest live-finalization-resumes-the-ordinary-run-cursor
  (let [rt (owned/runtime {:audit? true :cps-exit? true})
        callback (atom nil) results (atom [])
        spin (owned/cspin rt :parent
                          (let [a (next!)]
                            (owned/await-finalization (fn [resolve _] (reset! callback resolve)))
                            [a (next!)]))]
    (observe! rt spin results)
    (is (empty? @results))
    (is (fn? @callback))
    (when-let [resume @callback] (resume :ready))
    (let [a (successor (address/body-start-chain-head :parent))]
      (is (= [[a (successor a)]] @results)))
    (verify-boundaries! rt)))

#?(:clj
   (deftest retirement-during-hashing-refuses-the-address-commit
     (let [rt (owned/runtime {:cps-exit? true :audit? true})
           entered (promise) release (promise) reached-tail (atom false)
           blocked-site (assoc site :line 2)
           original-hash address/chain-hash results (atom [])
           spin (owned/cspin rt :parent
                             (address/next-address! ec/*execution-context* "spin" blocked-site)
                             (reset! reached-tail true))]
       (with-redefs [address/chain-hash
                     (fn [source previous]
                       (when (= blocked-site source)
                         (deliver entered true)
                         (when-not (= true (deref release 5000 ::timeout))
                           (throw (ex-info "Address hash test timed out" {}))))
                       (original-hash source previous))]
         (let [writer (future (observe! rt spin results))]
           (try
             (is (= true (deref entered 5000 ::timeout)))
             (let [canceller (future (owned/cancel-spin! rt spin))]
               (is (not= ::timeout (deref canceller 2000 ::timeout))
                   "Retirement can acquire the gate while address hashing is blocked"))
             (finally (deliver release true)))
           (is (not= ::timeout (deref writer 5000 ::timeout)))
           (is (false? @reached-tail))
           (is (= 1 (count @results)))))
       (is (= (successor nil) (address/next-address! rt "spin" site)))
       (verify-boundaries! rt))))

(deftest native-addressing-cannot-be-forged-through-application-state
  (let [rt (owned/runtime)]
    (doseq [path [[:addressing :chain-head] [:addressing :chain-heads :parent]
                  [:addressing :occurrences :parent]]]
      (is (thrown? #?(:clj Exception :cljs js/Error)
                   (rtp/swap-state! rt path (constantly :forged)))))
    (is (= (successor nil) (address/next-address! rt "spin" site)))))
