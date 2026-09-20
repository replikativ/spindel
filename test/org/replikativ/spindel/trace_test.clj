(ns org.replikativ.spindel.trace-test
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.savepoint :as sp :refer [savepoint]]
            [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :as aw]))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [outcome (deref result 5000 ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok (first outcome)) (second outcome) (throw (second outcome))))))

(defn- accumulate! [n]
  (rtp/swap-state! ec/*execution-context* [:test/acc] (fn [acc] (+ (or acc 0) n))))

(defn- program []
  (spin
   (let [a (savepoint :step 1)]
     (accumulate! a)
     (let [b (savepoint :step 2)]
       (accumulate! b)
       [a b (rtp/get-state ec/*execution-context* [:test/acc])]))))

(defn- branching-program []
  (spin
   (let [extra? (savepoint :flag true)
         extra (when extra? (savepoint :extra 1))]
     (loop [i 0 seen []]
       (if (< i 3)
         (recur (inc i) (conj seen (savepoint :item i)))
         {:extra extra :items seen})))))

(defmacro ^:private with-session [[root session] & body]
  `(let [~root (context/create-execution-context)
         ~session (sp/open! ~root {:seed 7 :fork-opts {:systems :none}})]
     (try
       ~@body
       (finally
         (await-cps (sp/close! ~session))
         (context/stop-context! ~root)))))

(defn- values-by-site [trace]
  (mapv (fn [address]
          (let [{:keys [site value]} (get-in trace [:trace/entries address])]
            [site value]))
        (:trace/order trace)))

(deftest run-records-every-site-in-program-order
  (with-session [root session]
    (let [trace (await-cps (trace/run session
                                      (binding [ec/*execution-context* root] (program))
                                      trace/payload-policy))]
      (is (= [1 2 3] (:trace/result trace)))
      (is (= [[:step 1] [:step 2]] (values-by-site trace)))
      (is (every? (comp sp/pending? :savepoint) (vals (:trace/entries trace)))))))

(deftest replay-reuses-upstream-and-reruns-downstream
  (with-session [root session]
    (let [original (await-cps (trace/run session
                                         (binding [ec/*execution-context* root] (program))
                                         trace/payload-policy))
          [first-address second-address] (:trace/order original)]
      (testing "changing the second site keeps the first, and what it accumulated"
        (let [replayed (await-cps
                        (trace/replay original second-address
                                      (trace/constrained-policy
                                       {second-address 20}
                                       (trace/keep-policy trace/payload-policy))))]
          (is (= [1 20 21] (:trace/result replayed)))
          (is (= [[:step 1] [:step 20]] (values-by-site replayed)))
          (is (identical? (get-in original [:trace/entries first-address])
                          (get-in replayed [:trace/entries first-address])))))
      (testing "changing the first site keeps the old value of the second"
        (let [replayed (await-cps
                        (trace/replay original first-address
                                      (trace/constrained-policy
                                       {first-address 10}
                                       (trace/keep-policy trace/payload-policy))))]
          (is (= [10 2 12] (:trace/result replayed)))))
      (testing "the replayed trace is a value"
        (is (= [1 2 3] (:trace/result original)))
        (is (= [[:step 1] [:step 2]] (values-by-site original)))))))

(deftest replay-prunes-sites-that-are-not-reached-again
  (with-session [root session]
    (let [original (await-cps (trace/run session
                                         (binding [ec/*execution-context* root]
                                           (branching-program))
                                         trace/payload-policy))
          flag (first (:trace/order original))
          replayed (await-cps
                    (trace/replay original flag
                                  (trace/constrained-policy
                                   {flag false}
                                   (trace/keep-policy
                                    ;; a site the old trace did not have
                                    (fn [sp _] {:value [:fresh (:savepoint/payload sp)]})))))]
      (is (= {:extra 1 :items [0 1 2]} (:trace/result original)))
      (is (= {:extra nil :items [0 1 2]} (:trace/result replayed)))
      (is (= [:flag :item :item :item] (mapv first (values-by-site replayed))))
      (testing "and brings them back, decided afresh"
        (let [again (await-cps
                     (trace/replay replayed flag
                                   (trace/constrained-policy
                                    {flag true}
                                    (trace/keep-policy
                                     (fn [sp _] {:value [:fresh (:savepoint/payload sp)]})))))]
          (is (= {:extra [:fresh 1] :items [0 1 2]} (:trace/result again))))))))

(deftest a-policy-may-write-to-the-world-it-decides
  (with-session [root session]
    (let [scoring (fn [sp _]
                    (rtp/swap-state! (:savepoint/world sp) [:test/score]
                                     (fn [score] (+ (or score 0) (:savepoint/payload sp))))
                    {:value (:savepoint/payload sp)
                     :note {:score (:savepoint/payload sp)}})
          original (await-cps (trace/run session
                                         (binding [ec/*execution-context* root] (program))
                                         scoring))
          second-address (second (:trace/order original))
          replayed (await-cps (trace/replay original second-address scoring))]
      (is (= 3 (rtp/get-state (:trace/world original) [:test/score])))
      (testing "the score before the site is still there after a replay from it"
        (is (= 3 (rtp/get-state (:trace/world replayed) [:test/score])))))))

(deftest release-abandons-what-the-winner-does-not-share
  (with-session [root session]
    (let [original (await-cps (trace/run session
                                         (binding [ec/*execution-context* root] (program))
                                         trace/payload-policy))
          [first-address second-address] (:trace/order original)
          replayed (await-cps (trace/replay original second-address
                                            (trace/keep-policy trace/payload-policy)))]
      (trace/release! replayed original)
      (is (sp/pending? (get-in original [:trace/entries first-address :savepoint])))
      (is (sp/pending? (get-in original [:trace/entries second-address :savepoint]))
          "the replayed site shares the original's anchor"))))

(deftest a-failing-computation-is-a-trace-with-an-error
  (with-session [root session]
    (let [trace (await-cps
                 (trace/run session
                            (binding [ec/*execution-context* root]
                              (spin (let [a (savepoint :step 1)]
                                      (throw (ex-info "boom" {:a a})))))
                            trace/payload-policy))]
      (is (= "boom" (ex-message (:trace/error trace))))
      (is (= [[:step 1]] (values-by-site trace))))))

(deftest a-spin-in-another-world-awaits-runs-and-replays
  ;; The controller lives in one world, the computation and its forks in
  ;; others: every completion crosses a world boundary on its way back.
  (let [controller (context/create-execution-context)
        root (context/create-execution-context)
        session (sp/open! root {:seed 7 :fork-opts {:systems :none}})]
    (try
      (let [outcome
            (binding [ec/*execution-context* controller]
              (deref
               (spin
                (let [original (aw/await (trace/run session
                                                    (binding [ec/*execution-context* root]
                                                      (program))
                                                    trace/payload-policy))
                      address (second (:trace/order original))
                      replayed (aw/await (trace/replay original address
                                                       (trace/constrained-policy
                                                        {address 20}
                                                        trace/payload-policy)))]
                  [(:trace/result original) (:trace/result replayed)]))
               10000 ::timeout))]
        (is (= [[1 2 3] [1 20 21]] outcome)))
      (finally
        (await-cps (sp/close! session))
        (context/stop-context! root)
        (context/stop-context! controller)))))
