(ns org.replikativ.spindel.v2.savepoint-layer-test
  "The v2 savepoint session layer (org.replikativ.spindel.v2.savepoint)."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.savepoint :as sp]))

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 400) false :else (do (Thread/sleep 5) (recur (inc n))))))

(defn- ends []
  (let [a (atom [])]
    [a {sp/result-site (fn [e] (swap! a conj [:result (:savepoint/payload e) (:savepoint/world e)]))
        sp/error-site (fn [e] (swap! a conj [:error (:savepoint/world e)]))
        sp/abandoned-site (fn [e] (swap! a conj [:abandoned (:savepoint/world e)]))}]))

(deftest no-handler-is-identity
  (let [w (v2/world) [es hs] (ends) s (sp/open! w {:handlers hs})]
    (sp/start! s #(task (inc (sp/savepoint :site 41))))
    (is (wait-until #(seq @es)))
    (is (= [:result 42 w] (first @es)))
    (sp/close! s)))

(deftest resume-in-place-with-an-address
  (let [w (v2/world) seen (atom nil) [es hs] (ends)
        s (sp/open! w {:handlers (assoc hs :choose (fn [p] (reset! seen p) (sp/resume p (* 10 (:savepoint/payload p)))))})]
    (sp/start! s #(task (inc (sp/savepoint :choose 4))))
    (is (wait-until #(seq @es)))
    (is (= [:result 41 w] (first @es)))
    (let [[frame key] (:savepoint/address @seen)]
      (is (= [] frame))
      (is (integer? key)))
    (is (not (sp/pending? @seen)))
    (sp/close! s)))

(deftest explicit-ids
  (let [w (v2/world) seen (atom nil)
        s (sp/open! w {:handlers {:choose (fn [p] (reset! seen p) (sp/resume p 1))}})]
    (sp/start! s #(task (sp/savepoint :choose nil {:id [:x 3]})))
    (is (wait-until #(some? @seen)))
    (is (= [:x 3] (:savepoint/address @seen)))
    (sp/close! s)))

(deftest forks-are-independent-particles-with-their-own-seeds
  (let [w (v2/world) pending (atom nil) [es hs] (ends)
        s (sp/open! w {:seed 7 :handlers (assoc hs :choose (fn [p] (reset! pending p)))})]
    (sp/start! s #(task (+ 100 (sp/savepoint :choose nil))))
    (is (wait-until #(some? @pending)))
    (let [p @pending
          kids (mapv (fn [_] (sp/fork p)) (range 3))]
      (is (sp/pending? p) "forking leaves the source pending")
      (is (every? sp/pending? kids))
      (is (= 3 (count (set (map #(sp/seed (:savepoint/world %)) kids)))) "derived seeds differ")
      (doseq [[k v] (map vector kids [1 2 3])] (sp/resume k v))
      (is (wait-until #(= 3 (count @es))))
      (is (= #{101 102 103} (set (map second @es))))
      (is (every? #(not= w (nth % 2)) @es) "each ends in its own world")
      (sp/abandon p)
      (is (wait-until #(= 4 (count @es))))
      (is (= :abandoned (first (last @es)))))
    (sp/close! s)))

(deftest copy-consumes-the-source
  (let [w (v2/world) pending (atom nil) [es hs] (ends)
        s (sp/open! w {:handlers (assoc hs :choose (fn [p] (reset! pending p)))})]
    (sp/start! s #(task (* 2 (sp/savepoint :choose nil))))
    (is (wait-until #(some? @pending)))
    (let [p @pending
          [a b] (sp/copy p 2)]
      (is (not (sp/pending? p)))
      (is (thrown? Exception (sp/resume p 1)))
      (sp/resume a 5) (sp/resume b 6)
      (is (wait-until #(= 2 (count @es))))
      (is (= #{10 12} (set (map second @es)))))
    (sp/close! s)))

(deftest an-unactivated-fork-is-abandoned-without-running
  (let [w (v2/world) pending (atom nil) ran (atom 0)
        s (sp/open! w {:handlers {:choose (fn [p] (reset! pending p))}})]
    (sp/start! s #(task (try (sp/savepoint :choose nil) (finally (swap! ran inc)))))
    (is (wait-until #(some? @pending)))
    (let [k (sp/fork @pending)]
      (sp/abandon k)
      (is (not (sp/pending? k)))
      (Thread/sleep 50)
      (is (zero? @ran) "nothing ran in the discarded fork"))
    (sp/close! s)))
