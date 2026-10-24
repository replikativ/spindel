(ns org.replikativ.spindel.trace-update-test
  "trace/update: re-run one key's spin of a keyed loop in a fork of the
  world a trace ended in — only that key's sites are decided again, what
  awaits the loop follows, and the source trace is untouched."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.savepoint :as sp :refer [savepoint]]
            [org.replikativ.spindel.trace :as trace]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.keyed :refer [keyed]]
            [org.replikativ.spindel.effects.await :as aw]))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [outcome (deref result 10000 ::timeout)]
      (when (= ::timeout outcome)
        (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok (first outcome)) (second outcome) (throw (second outcome))))))

(defn- item [i]
  (spin
   (let [a (savepoint :a {:i i :v i} {:id [:items i :a]})
         extra (when (odd? a) (savepoint :extra 1 {:id [:items i :extra]}))]
     (+ a (or extra 0)))))

(defn- program [n]
  (spin
   (let [head (savepoint :head 0 {:id :head})
         xs (aw/await (keyed :items (range n) item))]
     [head (reduce + xs)])))

(defn- by-payload [sp _old] {:value (:v (:savepoint/payload sp) (:savepoint/payload sp))})

(defmacro ^:private with-session [[root session] & body]
  `(let [~root (context/create-execution-context)
         ~session (sp/open! ~root {:seed 7 :fork-opts {:systems :none}})]
     (try
       ~@body
       (finally
         (await-cps (sp/close! ~session))
         (context/stop-context! ~root)))))

(deftest update-re-runs-one-key
  (with-session [root session]
    (let [n 6
          original (await-cps (trace/run session (binding [ec/*execution-context* root] (program n))
                                         by-payload {:anchor? #(= :head (:savepoint/address %))}))
          decided (atom [])
          set-a (fn [i v] (fn [sp old]
                            (swap! decided conj (:savepoint/address sp))
                            (if (= [:items i :a] (:savepoint/address sp))
                              {:value v}
                              (if old (select-keys old [:value]) (by-payload sp old)))))
          owner (fn [t i] (get-in t [:trace/entries [:items i :a] :spin]))]
      (is (= [0 (+ (reduce + (range n)) 3)] (:trace/result original)) "odd keys add their extra site")
      (testing "a value change in one key"
        (let [t (await-cps (trace/update original [(owner original 2)] (set-a 2 10)))]
          (is (= [[:items 2 :a]] @decided) "only that key's site was decided")
          (is (= [0 (+ (reduce + (range n)) 3 8)] (:trace/result t)) "the loop and its awaiter followed")
          (is (= 10 (get-in t [:trace/entries [:items 2 :a] :value])))
          (is (= (:trace/order original) (:trace/order t)) "program order kept")
          (is (= 2 (get-in original [:trace/entries [:items 2 :a] :value])) "the source trace is untouched")))
      (testing "a change that makes a site appear (birth) and one that removes it (death)"
        (reset! decided [])
        (let [born (await-cps (trace/update original [(owner original 2)] (set-a 2 5)))]
          (is (contains? (:trace/entries born) [:items 2 :extra]))
          (is (= [0 (+ (reduce + (range n)) 3 3 1)] (:trace/result born)))
          (reset! decided [])
          (let [died (await-cps (trace/update born [(owner born 3)] (set-a 3 4)))]
            (is (not (contains? (:trace/entries died) [:items 3 :extra])) "key 3's extra site is gone")
            (is (= (dec (count (:trace/order born))) (count (:trace/order died))))
            (is (= [0 (+ (reduce + (range n)) 3 3 1 1 -1)] (:trace/result died)))))))))

(deftest update-drops-anchors-after-the-first-change
  (with-session [root session]
    (let [original (await-cps (trace/run session (binding [ec/*execution-context* root] (program 3))
                                         by-payload {:anchor? #(= :head (:savepoint/address %))}))
          t (await-cps (trace/update original
                                     [(get-in original [:trace/entries [:items 1 :a] :spin])]
                                     (fn [sp old] (if (= [:items 1 :a] (:savepoint/address sp)) {:value 7} (select-keys old [:value])))))]
      (is (some? (get-in t [:trace/entries :head :savepoint])) "upstream anchors are kept")
      (is (nil? (get-in t [:trace/entries [:items 1 :a] :savepoint]))))))

;; --- review cases --------------------------------------------------------------

(defn- outcome
  ([operation] (outcome operation 5000))
  ([operation ms]
   (let [result (promise)]
     (operation #(deliver result [:ok %]) #(deliver result [:error %]))
     (deref result ms [:timeout nil]))))

(defn- erring-item [i]
  (spin
   (let [a (savepoint :a {:i i :v i} {:id [:items i :a]})]
     (when (= a :boom) (throw (ex-info "model error" {})))
     a)))

(defn- erring-program [n]
  (spin
   (let [xs (aw/await (keyed :items (range n) erring-item))]
     (reduce + (remove keyword? xs)))))

(defn- run-original [root session make-program]
  (await-cps (trace/run session (binding [ec/*execution-context* root] (make-program))
                        by-payload {:anchor? (constantly false)})))

(defn- owner [t i] (get-in t [:trace/entries [:items i :a] :spin]))

(defn- keep-but [address value]
  (fn [sp old] (if (= address (:savepoint/address sp)) value (select-keys old [:value]))))

(deftest an-asynchronous-policy-is-waited-for
  ;; the update is not quiescent while a site's policy is deciding
  (with-session [root session]
    (let [original (run-original root session #(erring-program 4))
          policy (keep-but [:items 2 :a] (fn [resolve _] (future (Thread/sleep 100) (resolve {:value 10}))))
          [k t] (outcome (trace/update original [(owner original 2)] policy))]
      (is (= :ok k))
      (is (= 10 (get-in t [:trace/entries [:items 2 :a] :value])))
      (is (= (+ 0 1 10 3) (:trace/result t))))))

(deftest two-keys-in-one-update
  (with-session [root session]
    (let [original (run-original root session #(erring-program 4))
          policy (fn [sp old] (case (:savepoint/address sp)
                                [:items 1 :a] {:value 10}
                                [:items 2 :a] {:value 20}
                                (select-keys old [:value])))
          [k t] (outcome (trace/update original [(owner original 1) (owner original 2)] policy))]
      (is (= :ok k))
      (is (= (+ 0 10 20 3) (:trace/result t))))))

(deftest a-model-error-ends-in-the-trace
  ;; as for `run`: the computation's error is the trace's, not the update's
  (with-session [root session]
    (let [original (run-original root session #(erring-program 3))
          [k t] (outcome (trace/update original [(owner original 1)] (keep-but [:items 1 :a] {:value :boom})))]
      (is (= :ok k))
      (is (= "model error" (some-> (:trace/error t) ex-message))))))

(deftest closing-the-session-rejects-a-running-update
  (let [root (context/create-execution-context)
        session (sp/open! root {:seed 7 :fork-opts {:systems :none}})
        original (run-original root session #(erring-program 3))
        p (promise)]
    ((trace/update original [(owner original 1)]
                   (keep-but [:items 1 :a] (fn [resolve _] (future (Thread/sleep 300)
                                                                   (try (resolve {:value 5}) (catch Throwable _ nil))))))
     #(deliver p [:ok %]) #(deliver p [:error %]))
    (Thread/sleep 20)
    (is (= :ok (first (outcome (sp/close! session) 5000))) "close! completes")
    (is (= :error (first (deref p 5000 [:timeout]))) "the update rejects")
    (context/stop-context! root)))

(defn- nesting-item [i]
  (spin
   (let [a (savepoint :a {:i i :v i} {:id [:items i :a]})
         x (if (odd? a) (aw/await (spin (savepoint :x 1 {:id [:items i :x]}))) 0)]
     (+ a x))))

(deftest sites-of-a-nested-spin-that-is-gone-are-removed
  (with-session [root session]
    (let [original (run-original root session #(spin (reduce + (aw/await (keyed :items (range 3) nesting-item)))))
          _ (is (contains? (:trace/entries original) [:items 1 :x]))
          [k t] (outcome (trace/update original [(owner original 1)] (keep-but [:items 1 :a] {:value 2})))]
      (is (= :ok k))
      (is (not (contains? (:trace/entries t) [:items 1 :x])))
      (is (= (+ 0 2 2) (:trace/result t))))))

(deftest an-address-of-another-key-is-a-duplicate
  (with-session [root session]
    (let [mk (fn [i] (spin (let [a (savepoint :a {:i i :v i} {:id [:items i :a]})]
                             (if (= a 99) (savepoint :b 5 {:id [:items 0 :a]}) a))))
          original (run-original root session #(spin (reduce + (aw/await (keyed :items (range 3) mk)))))
          [k e] (outcome (trace/update original [(owner original 2)]
                                       (fn [sp old] (if (= [:items 2 :a] (:savepoint/address sp))
                                                      {:value 99}
                                                      (if old (select-keys old [:value]) {:value 5})))))]
      (is (= :error k))
      (is (= ::trace/duplicate-address (:type (ex-data e)))))))
