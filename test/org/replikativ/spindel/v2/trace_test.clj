(ns org.replikativ.spindel.v2.trace-test
  "Traces and replay on v2 (org.replikativ.spindel.v2.trace)."
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.savepoint :as sp]
            [org.replikativ.spindel.v2.trace :as trace]))

(defn- run-op [op]
  (let [p (promise)]
    (op #(deliver p [:ok %]) #(deliver p [:err %]))
    (deref p 5000 [:timeout])))

(defn- program []
  (task (let [a (sp/savepoint :choose 1 {:id :a})
              b (sp/savepoint :choose 2 {:id :b})
              c (sp/savepoint :choose 3 {:id :c})]
          [a b c])))

(deftest run-records-every-site-in-order
  (let [w (v2/world) s (sp/open! w)
        [k t] (run-op (trace/run s program trace/payload-policy))]
    (is (= :ok k))
    (is (= [1 2 3] (:trace/result t)))
    (is (= [:a :b :c] (:trace/order t)))
    (is (= 2 (get-in t [:trace/entries :b :value])))
    (is (every? sp/anchor? (keep :savepoint (vals (:trace/entries t)))))
    (sp/close! s)))

(deftest replay-from-an-address-reuses-upstream-and-asks-downstream
  (let [w (v2/world) s (sp/open! w)
        [_ t] (run-op (trace/run s program trace/payload-policy))
        asked (atom [])
        policy (fn [sp old] (swap! asked conj (:savepoint/address sp))
                 (if (= :b (:savepoint/address sp)) {:value 20} {:value (:value old)}))
        [k t2] (run-op (trace/replay t :b policy))]
    (is (= :ok k))
    (is (= [1 20 3] (:trace/result t2)))
    (is (= [:b :c] @asked) "upstream :a is reused, not decided again")
    (is (= [:a :b :c] (:trace/order t2)))
    (is (= [1 2 3] (:trace/result t)) "the original trace is unchanged")
    (is (= :c (trace/earliest t2 #{:c :b2})))
    (trace/release! t t2)
    (is (not (sp/anchor? (get-in t [:trace/entries :c :savepoint]))) "the loser's own anchors are disposed")
    (is (sp/anchor? (get-in t2 [:trace/entries :a :savepoint])) "a shared upstream anchor survives")
    (sp/close! s)))

(deftest until-parks-a-decided-site
  (let [w (v2/world) s (sp/open! w)
        [k t] (run-op (trace/run s program trace/payload-policy {:until #(= :b (:savepoint/address %))}))]
    (is (= :ok k))
    (is (= 2 (:trace/pending-value t)))
    (is (sp/pending? (:trace/pending t)))
    (trace/release! t)
    (is (not (sp/pending? (:trace/pending t))))
    (sp/close! s)))

(deftest constrained-policy-fixes-addresses
  (let [w (v2/world) s (sp/open! w)
        [_ t] (run-op (trace/run s program (trace/constrained-policy {:c 30} trace/payload-policy)))]
    (is (= [1 2 30] (:trace/result t)))
    (sp/close! s)))
