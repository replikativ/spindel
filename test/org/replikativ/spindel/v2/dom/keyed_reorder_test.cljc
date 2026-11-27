(ns org.replikativ.spindel.v2.dom.keyed-reorder-test
  "The keyed memo under a turn budget (phase-d design §4.3, §8 P6): a
   keyed list of 12 items rendered with `{:budget 8}`, so every render is
   handed off across turns (on Node: macrotasks), is reversed and then
   rotated. No item reruns, each li element moves with its key, and the
   committed DOM order is the source order after each write, one commit
   per write. The JVM runs it on an inline and a non-inline world."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.v2.dom.elements :as el]
            [org.replikativ.spindel.v2.dom.foreach :refer [ifor-each]]
            [org.replikativ.spindel.v2.dom.render :as render]
            [org.replikativ.spindel.v2.dom.mock :as mock]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(defn- items [n] (mapv (fn [i] {:id i :v (str "item " i)}) (range n)))

(defn- rotate [v n] (into (subvec v n) (subvec v 0 n)))

(defn- delta
  "The runs since `before`, keys with no run left out."
  [runs before]
  (into {} (keep (fn [[k n]] (let [d (- n (get before k 0))] (when (pos? d) [k d])))) runs))

(defn- reorder-case [opts]
  (fx/async-world
   opts
   (fn [env done]
     (let [m (mock/make-mock)
           d (:discharge m)
           log (:log m)
           xs0 (items 12)
           xs (v2/signal xs0)
           runs (atom {})
           root (spin (el/ul (ifor-each :id (track xs)
                                        (fn [x] (swap! runs update (:id x) (fnil inc 0)) (el/li (:v x))))))
           {:keys [state unmount!]} (render/render! :container root d)
           lis #(mock/children d (first (mock/children d :container)))
           texts #(mapv last (drop 2 (first (mock/dom d :container))))
           reversed (vec (reverse xs0))
           steps [["reverse" reversed]
                  ["rotate left by 3" (rotate reversed 3)]
                  ["rotate right by 1" (rotate (rotate reversed 3) 11)]]]
       (swap! (:cleanups env) conj #(fx/call! env unmount!))
       (fx/on-revision
        env state 1
        (fn [x]
          (is (= :ok x))
          (fx/later
           (fn []
             (is (= (mapv :v xs0) (texts)) "the mount commits the source order")
             (is (= (zipmap (range 12) (repeat 1)) @runs) "each item runs once")
             (let [el-of (zipmap (map :id xs0) (lis))]
               ((fn step [rev [[label order] & more]]
                  (if-not label
                    (do (is (fx/call! env #(v2/idle? (:w env))) "nothing stranded: the world is idle")
                        (fx/call! env unmount!)
                        (is (empty? (fx/leftovers {:mock m} state)))
                        (done))
                    (let [before @runs]
                      (reset! log [])
                      (v2/write! xs order)
                      (fx/on-revision
                       env state (inc rev)
                       (fn [x]
                         (is (= :ok x))
                         (fx/later
                          (fn []
                            (testing label
                              (is (= (mapv :v order) (texts)) "the committed DOM order is the source order")
                              (is (= {} (delta @runs before)) "no item reruns")
                              (is (= (mapv (comp el-of :id) order) (lis)) "each li element moves with its key")
                              (is (empty? (filter #(= :create-element (:op %)) @log)) "no element is created")
                              (is (= (inc rev) (render/revision state)) "one commit for the write"))
                            (step (inc rev) more))))))))
                1 steps))))))))))

(deftest reverse-and-rotate-rerun-no-item
  #?(:clj (doseq [opts [{:budget 8} {:inline? false :budget 8}]]
            (testing (pr-str opts) (reorder-case opts)))
     :cljs (reorder-case {:budget 8})))
