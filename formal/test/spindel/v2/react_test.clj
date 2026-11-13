(ns spindel.v2.react-test
  "Loading spindel.v2.react kernel-checks obligations P8 (`react-done-ok`: the reactivation worklist empties
  within react-fuel) and P6 (`valid-done-ok`: the §3.4 validation walk ends within valid-fuel); the P8 flag
  runs as a tripwire for every computation of the random drivers' worlds; `p6-validity-chain` is the
  regression for the validation-fuel model bug (exponential walk, fixed by expanding each idle computation
  once)."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.react :as rx]
            [spindel.v2.engine-test :as et]
            [spindel.v2.inv-test :as it]))

(def theorems '[react-run8-world ck8-react-edges vm-react vm8-react-one react-run8-done vm-le-all react-done-ok
                useen-add valid-ex-done init-bound valid-done-ok])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

(defn drive [seed runs steps d0?]
  (let [rng (java.util.Random. seed)]
    (dotimes [run runs]
      (loop [i 0 w (et/prefix-world)]
        (when (< i steps)
          (let [item (loop [k 0]
                       (let [x (et/random-item rng w)]
                         (if (or (not d0?) (it/d0-ok? w x) (> k 50)) x (recur (inc k)))))
                w2 (:world (en/world-step w item))]
            (doseq [c (:comps w2)]
              (is (true? (rx/react-done w2 (:id c))) (str "react-done seed " seed " run " run " step " i " comp " (:id c))))
            (recur (inc i) w2)))))))

(deftest react-done-random
  (drive 20261191 10 50 false)
  (drive 20261192 10 50 true))

;; ---------------------------------------------------------------------------
;; P6 (model bug found by branch z57, fixed in engine.clj `valid-loop`): validation walked every path of
;; the validity DAG. The bottom computation tracks signal 3; three computations above it each await the
;; previous at four sites (validity: four entries on the previous); unobserving all four demotes them.
;; Observing the top validates the chain: 4 + 16 + 64 + 64 entries along all paths, beyond the former fuel
;; 1 + 13 x (1 + 5) = 79, so the top was declared invalid (epoch step, re-run) although nothing changed;
;; the engine's recursive validate! reactivates each debtor once (it is then no longer idle) and finds it
;; valid. Now each idle computation's entries are expanded once (`seen`): the top is reactivated, live with
;; its old result.
(defn- step! [w item]
  (let [o (en/world-step w item)] (is (true? (:accepted o)) (pr-str item)) (:world o)))
(defn- p6-chain [n m]
  (let [mk (fn [w] (let [c (:next-id w) w (step! w [14 2 c [1] 1]) ob (:next-id w) w (step! w [4 c 1 ob])
                         r (:next-id w) w (step! w [17 c r]) w (step! w [21 r])] [w c ob r]))
        [w c0 ob0 r0] (mk (reduce step! s/empty-world it/base))
        w (step! w [3 r0 3 1 (:next-id w)])
        w (step! w [20 r0 1 5])]
    (loop [i 0 w w prev c0 obs [ob0] cs [c0]]
      (if (= i n)
        [w prev obs cs]
        (let [[w c ob r] (mk w)
              w (reduce (fn [w _] (step! w [18 r [prev] 0 1 (:next-id w) []])) w (range m))
              w (step! w [20 r 1 (+ 6 i)])]
          (recur (inc i) w c (conj obs ob) (conj cs c)))))))
(deftest p6-validity-chain
  (let [[w top obs cs] (p6-chain 3 4)
        w (reduce (fn [w ob] (step! w [5 ob])) w (reverse obs))
        c (first (filter #(= top (:id %)) (:comps w)))]
    (is (= 4 (count cs)))
    (is (every? :idle (filter #((set cs) (:id %)) (:comps w))) "all four demoted")
    (is (true? (en/valid-idle w c)) "valid within the fuel (each idle computation expanded once)")
    (is (true? (rx/valid-done w c)) "P6 flag")
    (let [w2 (step! w [4 top 1 (:next-id w)])
          c2 (first (filter #(= top (:id %)) (:comps w2)))]
      (is (= [false 1 1] ((juxt :idle :epoch :done-epoch) c2)) "31 reactivated with its result (no epoch step)")
      (is (every? #(not (:idle %)) (filter #((set cs) (:id %)) (:comps w2))) "the whole chain is reactivated"))))
