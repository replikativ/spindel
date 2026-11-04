(ns org.replikativ.spindel.v2.core-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track await]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)

(defn- vworld []
  (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (take 3 @*divergences*)))))

(defn- rows-by-type [w]
  (frequencies (map #(aget ^objects % rw/TYPE) (vals (aget ^objects w rw/W-REG)))))

(defn- census [w]
  (let [f (rows-by-type w)]
    {:comps (get f rw/T-COMP 0) :edges (get f rw/T-EDGE 0) :runs (get f rw/T-RUN 0)
     :sources (get f rw/T-SOURCE 0) :acts (get f rw/T-ACT 0)}))

(deftest signal-and-spin
  (checked (let [w (vworld)]
             (binding [v2/*world* w]
               (let [x (v2/signal 1)
                     c (spin (* 10 (iv/get-new (track x))))
                     seen (atom [])
                     unobserve (v2/observe! c (fn [v _] (swap! seen conj v)))]
                 (is (= [10] @seen))
                 (v2/write! x 2)
                 (is (= [10 20] @seen))
                 (v2/write! x 2)
                 (is (= [10 20] @seen) "unchanged result does not notify")
                 (unobserve)
                 (is (= 0 (:edges (census w))) "unobserve drops the dep edge")
                 (is (= 20 (v2/value c)) "idle computation validates"))))))
(deftest chain-and-diamond
  (checked (let [w (vworld)]
             (binding [v2/*world* w]
               (let [x (v2/signal 1)
                     runs (atom 0)
                     a (spin (inc (iv/get-new (track x))))
                     b (spin (* 2 (await a)))
                     c (spin (* 3 (await a)))
                     d (spin (let [s (+ (await b) (await c))] (swap! runs inc) s))
                     seen (atom [])
                     _ (v2/observe! d (fn [v _] (swap! seen conj v)))]
                 (is (= [10] @seen))
                 (is (= 1 @runs))
                 (v2/write! x 2)
                 (is (= [10 15] @seen))
                 (is (= 2 @runs) "diamond runs its sink once per write"))))))
(deftest reentry-resumes-at-the-fired-site
  (checked (let [w (vworld)]
             (binding [v2/*world* w]
               (let [x (v2/signal 1)
                     y (v2/signal 10)
                     prefix (atom 0)
                     c (spin (swap! prefix inc)
                             (let [a (iv/get-new (track y))
                                   b (iv/get-new (track x))]
                               (+ a b)))
                     seen (atom [])
                     _ (v2/observe! c (fn [v _] (swap! seen conj v)))]
                 (v2/write! x 5)
                 (is (= [11 15] @seen))
                 (is (= 1 @prefix) "the prefix before the fired site does not rerun")
                 (v2/write! y 20)
                 (is (= [11 15 25] @seen))
                 (is (= 1 @prefix) "re-entry at the first site still skips the body start"))))))
(deftest conditional-dependency-is-released
  (checked (let [w (vworld)]
             (binding [v2/*world* w]
               (let [flag (v2/signal true)
                     x (v2/signal 1)
                     y (v2/signal 2)
                     c (spin (if (iv/get-new (track flag)) (iv/get-new (track x)) (iv/get-new (track y))))
                     seen (atom [])
                     _ (v2/observe! c (fn [v _] (swap! seen conj v)))]
                 (v2/write! flag false)
                 (is (= [1 2] @seen))
                 (v2/write! x 100)
                 (is (= [1 2] @seen) "the dropped branch no longer notifies")
                 (is (= 3 (:edges (census w))) "flag, y and the observe edge; no x edge"))))))
(deftest nested-children-are-adopted-and-released
  (checked (let [w (vworld)]
             (binding [v2/*world* w]
               (let [n (v2/signal 3)
                     child-runs (atom 0)
                     parent (spin (loop [i 0 acc 0]
                                    (if (< i (iv/get-new (track n)))
                                      (recur (inc i) (+ acc (await (spin (swap! child-runs inc) (* i i)))))
                                      acc)))
                     seen (atom [])
                     _ (v2/observe! parent (fn [v _] (swap! seen conj v)))]
                 (is (= [5] @seen))
                 (is (= 3 @child-runs))
                 (v2/write! n 4)
                 (is (= [5 14] @seen))
                 (is (= 4 @child-runs) "existing children are adopted, only the new one runs")
                 (v2/write! n 1)
                 (is (= [5 14 0] @seen))
                 (verify/gc-settle! w)
                 (let [{:keys [comps]} (census w)]
                   (is (<= comps 2) "released children are demoted and dropped once unreferenced")))))))
(deftest repeated-churn-is-bounded
  (checked (let [w (vworld)]
             (binding [v2/*world* w]
               (let [x (v2/signal 0)
                     parent (spin (let [v (iv/get-new (track x))]
                                    (await (spin (inc v)))))
                     _ (v2/observe! parent (fn [_ _]))]
                 (dotimes [i 200] (v2/write! x i))
                 (let [c (census w)]
                   (is (<= (:comps c) 3) (str "census " c))
                   (is (<= (:edges c) 4) (str "census " c))
                   (is (<= (:runs c) 2) (str "census " c))))))))

(deftest reactivation-on-a-closed-source-takes-no-edge
  ;; Z#51: the source closed while the computation was idle; its value is
  ;; still valid, so reactivation keeps the result and consumes the edge
  (checked
   (let [w (vworld)
         runs (atom 0)]
     (binding [v2/*world* w]
       (let [sig (promise)
             gate (v2/deferred)
             t (v2/task (do (deliver sig (v2/signal 5)) (await gate) :done))
             s (deref sig 1000 nil)
             c (spin (swap! runs inc) (* 2 (iv/get-new (track s))))
             seen (atom [])
             unobserve (v2/observe! c (fn [v _] (swap! seen conj v)))]
         (unobserve)
         (v2/deliver! gate :go)
         (is (= :done (v2/value t 1000 ::timeout)))
         (let [unobserve (v2/observe! c (fn [v _] (swap! seen conj v)))]
           (is (= [10 10] @seen) "the result is reused")
           (is (= 1 @runs) "no re-run")
           (is (= 1 (:edges (census w))) "only the observe edge remains")
           (unobserve)))))))

(deftest no-fired-sibling-outlives-a-reentry
  ;; Z#59 (the model's L5 counterexample): a group await gives two dep edges at
  ;; one site; both fire; the re-run does not await again. No fired sibling
  ;; may survive, and a later write must not mark the creditor forever.
  (checked
   (let [w (vworld) n (atom 0)]
     (binding [v2/*world* w]
       (let [a (v2/signal 1) b (v2/signal 2)
             c (spin (if (= 1 (swap! n inc)) (v2/await-all [a b]) :no-await))
             d (spin [:saw (await c)])
             seen (atom [])]
         (v2/observe! d (fn [v _] (swap! seen conj v)))
         (v2/call-in! w #(do (v2/write! a 10) (v2/write! b 20)))   ; both fire in one item
         (is (= [:saw :no-await] (v2/value d 1000 ::timeout)))
         (is (= [[true] []]
                (v2/call-in! w #(mapv (fn [x] (mapv (fn [e] (boolean (aget ^objects e rw/E-ARMED)))
                                                    (aget ^objects (v2/row-of x) rw/OUTS)))
                                      [a b])))
             "E (on a) is re-armed by the restart; its fired sibling (on b) was cut")
         (v2/write! b 30)
         (is (= [:saw :no-await] (v2/value d 1000 ::timeout)) "the creditor settles after a later write")
         (is (zero? (v2/call-in! w #(aget ^objects (v2/row-of d) rw/C-PENDING))) "nothing is left pending"))))))
