(ns org.replikativ.spindel.v2.world-order-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]))

(def max-word 4294967295)
(defn- order [w] (aget ^objects w rw/W-CREATION))
(defn- close! [w] (v2/close-world! (v2/world-host-owner w) w))

(deftest exact-order-carry-precision-and-clean-exhaustion
  (doseq [[before after] [[[0 0] [0 1]] [[0 max-word] [1 0]]
                          [[2097152 max-word] [2097153 0]]
                          [[max-word (dec max-word)] [max-word max-word]]]]
    (is (= after (#'v2/next-world-order before)))
    (is (neg? (compare before after))))
  (let [isolated (atom [max-word max-word])]
    (is (thrown? clojure.lang.ExceptionInfo (swap! isolated #'v2/next-world-order)))
    (is (= [max-word max-word] @isolated))))

(deftest creation-is-fresh-on-world-fork-basis-and-instance-and-stable-on-cow
  (let [p (v2/world) initial (order p) c (v2/fork! p) pubs (atom [])]
    (is (= initial (order p)))
    (is (neg? (compare initial (order c))))
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (let [t (task (v2/savepoint :s nil)) pub (first @pubs) basis (:basis pub)
            a (v2/instantiate pub) b (v2/instantiate pub)]
        (is (every? neg? (map compare [(order c) (order basis) (order a)]
                              [(order basis) (order a) (order b)])))
        (is (= initial (order p)))
        (close! a) (close! b)
        (v2/abandon! pub)
        (hs/fence! t)))
    (close! p)))

(deftest acquisition-exhaustion-preflights-host-and-effect-forks
  (let [p (v2/world) failure (atom nil) snapshots (atom nil)]
    (v2/call-in! p #(aset ^objects p rw/W-CLOSE
                          (assoc (aget ^objects p rw/W-CLOSE) :next-child [max-word max-word])))
    (let [epoch (aget ^objects p rw/W-EPOCH) rank @(deref #'v2/world-order)
          next-id (#'v2/peek-id p)]
      (is (thrown? clojure.lang.ExceptionInfo (v2/fork! p)))
      (is (identical? epoch (aget ^objects p rw/W-EPOCH)))
      (is (= rank @(deref #'v2/world-order)))
      (is (= next-id (#'v2/peek-id p))))
    (binding [v2/*world* p]
      (let [gate (v2/deferred) result (atom [])
            t (task
               (let [epoch (aget ^objects p rw/W-EPOCH) next-id (#'v2/peek-id p)
                     rank @(deref #'v2/world-order)]
                 (try (v2/fork)
                      (catch Throwable error (reset! failure (:spindel/invalid (ex-data error)))))
                 (reset! snapshots [(identical? epoch (aget ^objects p rw/W-EPOCH))
                                    (= next-id (#'v2/peek-id p)) (= rank @(deref #'v2/world-order))])
                 (await gate)
                 :healthy))]
        (is (= :world-acquisition-order-exhausted @failure))
        (is (= [true true true] @snapshots))
        (v2/value-async t (fn [v failed?] (swap! result conj [v failed?])))
        (v2/deliver! gate :go)
        (is (= [[:healthy false]] @result))))
    (close! p)))

(deftest global-order-refusal-precedes-source-fork-mutation
  (let [p (v2/world) epoch (aget ^objects p rw/W-EPOCH) next-id (#'v2/peek-id p)
        rank @(deref #'v2/world-order)]
    (with-redefs-fn {#'v2/allocate-world-order! #(throw (ex-info "exhausted" {:spindel/invalid :world-order-exhausted}))}
      #(is (thrown? clojure.lang.ExceptionInfo (v2/fork! p))))
    (is (identical? epoch (aget ^objects p rw/W-EPOCH)))
    (is (= next-id (#'v2/peek-id p)))
    (is (= rank @(deref #'v2/world-order)))
    (close! p)))

(deftest s4-acquisition-exhaustion-rejects-queued-work-and-keeps-real-host-debt
  (let [p (v2/world) pubs (atom []) submit (atom []) read (atom [])]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (let [t (task (v2/savepoint :s nil)) c (v2/instantiate (first @pubs))
            cap (v2/register-world-settlement! (v2/world-host-owner c) c [])]
        (v2/call-in! p #(aset ^objects p rw/W-CLOSE
                              (assoc (aget ^objects p rw/W-CLOSE) :next-child [max-word max-word])))
        (with-redefs-fn {#'v2/after-gate-action! (fn [f] (swap! submit conj f))}
          #(v2/activate! c :never))
        (v2/value-async (v2/in-world c t) (fn [v failed?] (swap! read conj [v failed?])))
        (doseq [f @submit] (f))
        (is (= 1 (count @read)))
        (is (:spindel/released (ex-data (ffirst @read))))
        (is (:execution-retired? (v2/world-close-status c)))
        (is (not (:terminal? (v2/world-close-status c))))
        (is (nil? (aget ^objects c rw/W-HOLDER)))
        (v2/acknowledge-world-settlement! cap {:settled? true :value :native-disposed})
        (close! p)))))
