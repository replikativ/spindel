(ns org.replikativ.spindel.v2.sci.running-clause-test
  "§2, B3, T11 for SCI bodies: an invalidation at a site inside a running
   finally clause restarts the body. Before, the rerun resumed the captured
   SCI continuation inside the clause, whose region stack the new run never
   entered (the adapter's `:running` entry against R-INFIN 0)."
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.running-clause-test :refer [balanced-finally?]]
            [org.replikativ.spindel.v2.sci.support :as s :refer [checked ev]]
            [org.replikativ.spindel.v2.verify :as verify]
            [sci.core :as sci]))

(deftest a-track-in-a-running-clause-restarts-the-body
  (checked
   (let [w (s/vworld)
         [sig d] (binding [v2/*world* w] [(v2/signal 0) (v2/deferred)])
         p (s/interpreter {:bindings {'sig sig 'd d}})
         seen (atom [])
         c (ev w p "(def log (atom []))
                    (spin (try (swap! log conj :body)
                               :v
                               (finally
                                 (let [x (:new (track sig))]
                                   (swap! log conj [:fin x])
                                   (when (= 1 x) (swap! log conj [:awaited (await d)]))))))")]
     (v2/observe! c (fn [v err?] (swap! seen conj [(if err? (:spindel/invalid (ex-data v)) v) err?])))
     (v2/write! sig 1)
     (is (s/wait-until #(= [[:v false] [:finalizer true]] @seen)) "the rerun's await in the clause is refused")
     (v2/deliver! d :late)
     (is (= [:body [:fin 0] :body [:fin 1]] (sci/eval-string* p "@log")) "the rerun started from the body")
     (is (balanced-finally? (verify/log w)))
     (v2/release-world! w)
     (is (true? (v2/await-complete w 5000 ::timeout))))))

(deftest an-await-in-a-running-clause-restarts-the-body
  (checked
   (let [w (s/vworld)
         sig (binding [v2/*world* w] (v2/signal 0))
         p (s/interpreter {:bindings {'sig sig}})
         inner (ev w p "(def log (atom [])) (def inner (spin (:new (track sig)))) inner")
         _ (v2/observe! inner (fn [_ _]))
         seen (atom [])
         c (ev w p "(spin (try (swap! log conj :body)
                               :v
                               (finally (swap! log conj [:fin (await inner)]))))")]
     (v2/observe! c (fn [v err?] (swap! seen conj [v err?])))
     (is (s/wait-until #(= [[:v false]] @seen)))
     (v2/write! sig 1)
     (is (s/wait-until #(= [:body [:fin 0] :body [:fin 1]] (sci/eval-string* p "@log"))) "the rerun started from the body")
     (is (balanced-finally? (verify/log w)))
     (v2/release-world! w)
     (is (true? (v2/await-complete w 5000 ::timeout))))))
