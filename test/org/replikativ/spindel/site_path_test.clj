(ns org.replikativ.spindel.site-path-test
  "Readable site paths: `:id` names — hierarchical ones as vectors — give
  savepoint sites Gen-style addresses a caller can name from outside, and
  every trace entry records its path."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.inference.trace :as itrace]
            [org.replikativ.spindel.inference.effects :refer [sample observe]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [anglican.runtime :as ar]))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [outcome (deref result 20000 ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok (first outcome)) (second outcome) (throw (second outcome))))))

(defn- run
  "Run the spin `(make)` under the scoring policy with `constraints`, in a
  root world and session of its own; returns the trace."
  ([make] (run make {}))
  ([make constraints]
   (let [root (context/create-execution-context)
         session (sp/open! root {:fork-opts {:systems :none} :retain-released? false})
         t (await-cps (trace/run session (binding [ec/*execution-context* root] (make))
                                 (itrace/policy {:constraints constraints})))]
     (await-cps (sp/close! session))
     t)))

(defn- steps []
  (spin
   (loop [i 0 xs []]
     (if (= i 3)
       xs
       (recur (inc i)
              (conj xs (sample (ar/normal 0.0 1.0) :id [:step i :x])))))))

(deftest a-hierarchical-name-is-the-address
  (let [t (run steps {[:step 1 :x] 0.5})]
    (is (= [[:step 0 :x] [:step 1 :x] [:step 2 :x]] (:trace/order t)))
    (is (= 0.5 (second (:trace/result t))) "constrained from outside, by path")
    (is (= [:step 1 :x] (get (trace/by-path t) [:step 1 :x])))))

(deftest a-scalar-name-is-its-own-address
  (let [t (run #(spin (sample (ar/normal 0.0 1.0) :id :top)))]
    (is (= [:top] (:trace/order t)))
    (is (= [:top] (get-in t [:trace/entries :top :path])))))

(defn- branchy []
  (spin
   (let [b (sample (ar/flip 0.5) :id :b)
         _ (when b (sample (ar/normal 0.0 1.0)))
         v (sample (ar/normal 0.0 1.0))]
     [b v])))

(deftest an-unnamed-site-keeps-its-address-across-an-upstream-branch
  (let [last-site (fn [t] (let [a (peek (:trace/order t))] [a (get-in t [:trace/entries a :path])]))
        [a1 p1] (last-site (run branchy {:b true}))
        [a2 p2] (last-site (run branchy {:b false}))]
    (is (= a1 a2))
    (is (= p1 p2))
    (testing "its path names the site: [site source-loc occurrence]"
      (is (= :inference/choose (first (peek p1))))
      (is (= 0 (peek (peek p1)))))))

(deftest a-name-reused-in-one-run-is-an-error
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Duplicate site address"
                        (run #(spin (loop [i 0]
                                      (when (< i 2)
                                        (sample (ar/normal 0.0 1.0) :id :x)
                                        (recur (inc i)))))))))
