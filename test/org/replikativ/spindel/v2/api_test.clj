(ns org.replikativ.spindel.v2.api-test
  "M6 phase A: host calls, world state, refs, atoms (.internal/m6-phase-a-design.md v2)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await]]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)

(defn- vworld []
  (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- outcome [h]
  (try [:ok (v2/value h 1000 ::timeout)] (catch Exception e [:err (ex-data e)])))

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 500) false :else (do (Thread/sleep 5) (recur (inc n))))))

;; --- R5 host-call! / send-world!, R7 value guard

(deftest host-call-returns-and-guards
  (checked
    (let [w (vworld) other (vworld)]
      (binding [v2/*world* w]
        (is (= 42 (v2/host-call! w (fn [] 42))) "a host item's value")
        (is (= [:ok :inside] (outcome (task (v2/host-call! (v2/current-world) (fn [] :inside)))))
            "inside its own world it runs at once")
        (is (= :host-call
               (:spindel/invalid (second (outcome (task (v2/host-call! other (fn [] 1)))))))
            "waiting on another world from a body is refused (B7)")
        (let [x (v2/signal other 0)]
          (is (= [:ok nil] (outcome (task (v2/send-world! other #(v2/write! x 7))))))
          (is (wait-until #(= 7 (v2/value x))) "send-world! enqueues and the item runs later"))))))

(deftest value-in-a-callback-is-refused
  (checked
    (let [w (vworld) seen (promise)]
      (binding [v2/*world* w]
        (let [x (v2/signal 1)
              c (spin (* 2 (iv/get-new (track x))))]
          (v2/observe! c (fn [_ _] (deliver seen (try (v2/value x) :read (catch Exception e (ex-message e))))))
          (is (re-find #"processing a world" (str (deref seen 1000 nil)))))))))

;; --- R1 world state and refs

(deftest world-state-forks-by-value
  (checked
    (let [w (vworld)]
      (v2/assoc-in-world! w [:room :name] "a")
      (is (= {:room {:name "a"}} (v2/world-state w)))
      (let [c (v2/fork! w)]
        (v2/assoc-in-world! c [:room :name] "b")
        (is (= "a" (v2/get-in-world w [:room :name])) "the parent is unchanged")
        (is (= "b" (v2/get-in-world c [:room :name])) "the child has its own")
        (v2/update-in-world! w [:n] (fnil inc 0))
        (is (nil? (v2/get-in-world c [:n])) "no write propagates after the fork")))))

(deftest world-state-refuses-handles-and-resolves-refs
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [x (v2/signal 1)]
          (is (= :world-state (:spindel/invalid (try (v2/assoc-in-world! w [:x] x) nil
                                                     (catch Exception e (ex-data e))))))
          (v2/assoc-in-world! w [:x] (v2/world-ref x))
          (let [c (v2/fork! w)
                cx (v2/resolve-ref c (v2/get-in-world c [:x]))]
            (v2/write! cx 2)
            (is (= 2 (v2/value cx)) "the ref resolves to the child's copy")
            (is (= 1 (v2/value (v2/resolve-ref w (v2/get-in-world w [:x])))) "the parent's is unchanged")))))))

(deftest world-state-in-a-body-acts-on-the-slice-world
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [t (task (v2/swap-world! (v2/current-world) assoc :from :task) :done)]
          (is (= [:ok :done] (outcome t)))
          (is (= :task (v2/get-in-world w [:from]))))))))

;; --- R6 atoms

(deftest atoms-have-atom-semantics
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [a (v2/atom 0)]
          (is (= 1 (swap! a inc)))
          (is (= 11 (swap! a + 10)))
          (is (= 0 (reset! a 0)))
          (is (true? (compare-and-set! a 0 5)))
          (is (false? (compare-and-set! a 0 6)))
          (is (= [5 6] (swap-vals! a inc)))
          (is (= 6 @a)))))))

(deftest atoms-are-fork-safe
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [a (v2/atom :parent)
              c (v2/fork! w)]
          (binding [v2/*world* c]
            (reset! a :child)
            (is (= :child @a)))
          (is (= :parent @a) "the parent keeps its value")
          (let [b (v2/atom 1)]
            (binding [v2/*world* c]
              (is (= 1 (:spindel/missing-state-id
                        (try @b nil (catch Exception e {:spindel/missing-state-id (if (:spindel/missing-state (ex-data e)) 1 0)}))))
                  "an atom made after the fork has no state in the child"))))))))

(deftest atoms-in-a-forked-body
  ;; the body copied into a fork acts on the fork's atom value
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [a (v2/atom 0)
              out (promise)
              gate (v2/deferred)
              t (task (let [[side child] (v2/fork)]
                        (swap! a + (if (= side :child) 100 1))
                        (when (= side :parent) (deliver out child) (await gate))
                        @a))
              child (deref out 1000 nil)]
          (is (= [:ok 100] (outcome (v2/in-world child t))) "the child's copy")
          (v2/deliver! gate :go)
          (is (= [:ok 1] (outcome t)) "the parent's own"))))))
