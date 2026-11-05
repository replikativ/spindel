(ns org.replikativ.spindel.v2.port.atom-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture api]]))

(use-fixtures :each checked-fixture)

(deftest test-atom-basic-operations
  (let [a (v2/atom [])]
    (is (= [] @a))
    (is (= [1] (swap! a conj 1))) (is (= [1] @a))
    (is (= [2 3] (reset! a [2 3]))) (is (= [2 3] @a))
    (is (= [2 3 4 5] (swap! a conj 4 5))) (is (= [2 3 4 5] @a))))

(deftest ^:gap test-atom-metadata
  (is (= {:doc "Test atom"} (meta ((api 'atom) [] :meta {:doc "Test atom"})))))

(deftest test-atom-in-spin-context
  (is (= [1 2] (v2/value (task (let [cache (v2/atom [])]
                                 (swap! cache conj 1)
                                 (swap! cache conj 2)))))))

(deftest ^:gap test-atom-watchers
  (let [a (v2/atom 0) calls (atom [])]
    (add-watch a :watch (fn [k _ old new] (swap! calls conj {:key k :old old :new new})))
    (swap! a inc)
    (is (= [{:key :watch :old 0 :new 1}] @calls))
    (remove-watch a :watch) (swap! a inc)
    (is (= 1 (count @calls)))))

(deftest test-atom-forking
  (let [a (v2/atom [1 2 3]) child (v2/fork! v2/*world*)]
    (try
      (binding [v2/*world* child]
        (is (= [1 2 3] @a)) (swap! a conj 4) (is (= [1 2 3 4] @a)))
      (is (= [1 2 3] @a)) (swap! a conj 5) (is (= [1 2 3 5] @a))
      (binding [v2/*world* child] (is (= [1 2 3 4] @a)))
      (finally (v2/release-world! child)))))

(deftest ^:gap test-atom-execution-context
  (let [a (v2/atom 42) calls (atom [])]
    (is (= 42 @a))
    (add-watch a :test-watcher (fn [k _ old new] (swap! calls conj {:key k :old old :new new})))
    (swap! a inc)
    (is (= 1 (count @calls)))
    (is (= 42 (:old (first @calls))))
    (is (= 43 (:new (first @calls))))))

(deftest ^:gap test-atom-backend-abstraction
  (let [atoms (mapv v2/atom [1 2 3]) calls (mapv (fn [_] (atom [])) atoms)]
    (is (= [1 2 3] (mapv deref atoms)))
    (doseq [[a seen] (map vector atoms calls)]
      (add-watch a :w (fn [k _ old new] (swap! seen conj [k old new])))
      (swap! a inc))
    (is (= [1 1 1] (mapv #(count @%) calls)))))

(deftest ^:gap test-fork-watcher-fires-on-fork-mutation
  (let [a (v2/atom 0) rc (atom []) fc (atom [])]

    (let [child (v2/fork! v2/*world*)]
      (try
        (binding [v2/*world* child]
          (add-watch a :fork (fn [_ _ o n] (swap! fc conj [o n])))
          (swap! a inc))
        (is (= [] @rc))
        (is (= [[0 1]] @fc))
        (swap! a inc)

        (finally (v2/release-world! child))))))

(deftest ^:gap test-fork-watcher-parent-stays-silent
  (let [a (v2/atom 0) rc (atom []) fc (atom [])]
    (add-watch a :root (fn [_ _ o n] (swap! rc conj [o n])))
    (let [child (v2/fork! v2/*world*)]
      (try
        (binding [v2/*world* child]

          (swap! a inc))
        (is (= [] @rc))

        (swap! a inc)
        (is (= [[0 1]] @rc))
        (finally (v2/release-world! child))))))

(deftest ^:gap test-fork-watcher-independence
  (let [a (v2/atom 0) rc (atom []) fc (atom [])]
    (add-watch a :root (fn [_ _ o n] (swap! rc conj [o n])))
    (let [child (v2/fork! v2/*world*)]
      (try
        (binding [v2/*world* child]
          (add-watch a :fork (fn [_ _ o n] (swap! fc conj [o n])))
          (swap! a inc))
        (is (= [] @rc))
        (is (= [[0 1]] @fc))
        (swap! a inc)
        (is (= [[0 1]] @rc))
        (finally (v2/release-world! child))))))

(deftest ^:gap test-restored-context-watcher-without-prior-atom
  (let [a (v2/atom 0) rc (atom []) fc (atom [])]

    (let [child (v2/fork! v2/*world*)]
      (try
        (binding [v2/*world* child]
          (add-watch a :fork (fn [_ _ o n] (swap! fc conj [o n])))
          (swap! a inc))
        (is (= [] @rc))
        (is (= [[0 1]] @fc))
        (swap! a inc)

        (finally (v2/release-world! child))))))

(deftest ^:gap atom-cas-identity-and-watch-semantics
  (let [initial (with-meta [:value] {:identity :first})
        equal-value (with-meta [:value] {:identity :second})
        a (v2/atom initial) calls (atom [])]
    (add-watch a :watch (fn [key ref old new]
                          (swap! calls conj [key (identical? a ref) old new @ref])))
    (is (false? (compare-and-set! a equal-value :wrong))) (is (empty? @calls))
    (is (true? (compare-and-set! a initial nil)))
    (is (= [[:watch true initial nil nil]] @calls))
    (is (true? (compare-and-set! a nil false)))
    (is (true? (compare-and-set! a false :done)))
    (is (= :done @a)) (is (= 3 (count @calls)))))

(deftest missing-cell-mutations-cannot-resurrect-state
  (let [a (v2/atom :initial) other (v2/world)]
    (try
      (binding [v2/*world* other]
        (is (thrown? Exception (reset! a :resurrected)))
        (is (thrown? Exception (add-watch a :watch (fn [& _]))))
        (is (thrown? Exception (remove-watch a :watch)))
        (is (thrown? Exception (deref a))))
      (is (= :initial @a))
      (finally (v2/release-world! other)))))

(deftest ^:gap watches-are-selected-at-value-commit
  (doseq [mutate! [(fn [a] (swap! a inc)) (fn [a] (compare-and-set! a 0 1))]]
    (let [a (v2/atom 0) calls (atom []) committed (promise) continue (promise)]
      (add-watch a :before (fn [k _ o n]
                             (deliver committed true)
                             (deref continue 5000 ::timeout)
                             (swap! calls conj [k o n])))
      (let [worker (future (mutate! a))]
        (try
          (is (true? (deref committed 5000 false)))
          ;; Queue registration changes while the committed callback is held.
          (let [changes (future (remove-watch a :before)
                                (add-watch a :after (fn [k _ o n] (swap! calls conj [k o n]))))]
            (deliver continue true)
            (is (not= ::timeout (deref changes 5000 ::timeout))))
          (finally (deliver continue true)))
        (is (not= ::timeout (deref worker 5000 ::timeout)))
        (is (= [[:before 0 1]] @calls))))))
