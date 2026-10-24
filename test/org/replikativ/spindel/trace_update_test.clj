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
