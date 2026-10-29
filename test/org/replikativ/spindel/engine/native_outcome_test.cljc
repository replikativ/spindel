(ns org.replikativ.spindel.engine.native-outcome-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]))

(defn payloads [] [nil false c/cancelled (c/->Failure :data) (c/->Failure nil)])
(defn errors [] #?(:clj [nil false :error] :cljs [nil false :error js/undefined]))

(deftest computation-payloads-do-not-select-the-error-channel
  (doseq [value (payloads)]
    (let [rt (c/runtime) values (atom []) errors (atom [])
          s (c/cspin rt :spin value)]
      (c/observe! rt s #(swap! values conj %) #(swap! errors conj %))
      (is (= [value] @values))
      (is (empty? @errors))
      (c/observe! rt s #(swap! values conj %) #(swap! errors conj %))
      (is (= [value value] @values))
      (is (empty? @errors)))))

(deftest parking-payloads-do-not-select-the-error-channel
  (doseq [value (payloads)]
    (let [rt (c/runtime) ticket (c/ticket :outside) values (atom []) errors (atom [])
          s (c/cspin rt :spin (c/park ticket))]
      (c/observe! rt s #(swap! values conj %) #(swap! errors conj %))
      (c/resume-ticket! rt (c/pending-ticket rt ticket) value)
      (is (= [value] @values))
      (is (empty? @errors)))))

(deftest awaited-payloads-are-opaque-both-cached-and-after-suspension
  (doseq [value (payloads) cached? [false true]]
    (let [rt (c/runtime) ticket (c/ticket :outside) values (atom []) errors (atom [])
          child (c/cspin rt :child (c/park ticket))
          parent (c/cspin rt :parent (c/await child))]
      (when cached?
        (c/observe! rt child (fn [_]) (fn [_]))
        (c/resume-ticket! rt (c/pending-ticket rt ticket) value))
      (c/observe! rt parent #(swap! values conj %) #(swap! errors conj %))
      (when-not cached? (c/resume-ticket! rt (c/pending-ticket rt ticket) value))
      (is (= [value] @values))
      (is (empty? @errors)))))

(deftest real-native-rejections-preserve-nullable-error-payloads
  (doseq [error (errors)]
    (let [rt (c/runtime) values (atom []) errors (atom [])
          s (c/cspin rt :spin (c/await-host (fn [_resolve reject] (reject error))))]
      (c/observe! rt s #(swap! values conj %) #(swap! errors conj %))
      (is (empty? @values))
      (is (= [error] @errors))
      (is (identical? error (first @errors)))
      (c/observe! rt s #(swap! values conj %) #(swap! errors conj %))
      (is (empty? @values))
      (is (= [error error] @errors))
      (is (identical? error (second @errors))))))

(deftest rejected-tickets-preserve-errors-through-cached-and-delayed-awaits
  (doseq [error (errors) cached? [false true]]
    (let [rt (c/runtime) ticket (c/ticket :outside) values (atom []) failures (atom [])
          child (c/cspin rt :child (c/park ticket))
          parent (c/cspin rt :parent (c/await child))]
      (when cached?
        (c/observe! rt child (fn [_]) (fn [_]))
        (c/reject-ticket! rt (c/pending-ticket rt ticket) error))
      (c/observe! rt parent #(swap! values conj %) #(swap! failures conj %))
      (when-not cached? (c/reject-ticket! rt (c/pending-ticket rt ticket) error))
      (is (empty? @values))
      (is (= [error] @failures))
      (is (identical? error (first @failures))))))
