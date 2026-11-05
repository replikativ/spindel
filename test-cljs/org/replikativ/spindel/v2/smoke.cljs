(ns org.replikativ.spindel.v2.smoke
  "Node smoke run of engine v2 (CLJS)."
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await await-all take!]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.incremental.interval :as iv]))

(defn -main []
  (let [w (v2/world)
        out (atom [])]
    (binding [v2/*world* w]
      (let [a (v2/atom 0) seen (atom [])]
        (v2/host-call! w #(binding [v2/*world* nil]
                            (add-watch a :k (fn [_ _ o n] (swap! seen conj [o n])))))
        (swap! a inc)
        (assert (= [[0 1]] @seen))
        (remove-watch a :k)
        (let [b (v2/atom 0)]
          (swap! a (fn [v] (swap! b inc) (inc v)))
          (assert (= 1 @b)))
        (let [other (v2/world)
              b (binding [v2/*world* other] (v2/atom :other))]
          (binding [v2/*world* other]
            (assert (contains? (try (reset! a :wrong) {} (catch :default e (ex-data e))) :spindel/missing-state))
            (assert (= :other @b)))))
      (let [p (comb/parallel (spin 10) (spin 20))]
        (v2/value-async p (fn [v err?] (assert (not err?)) (assert (= [10 20] v)))))
      (let [s (v2/signal :first)
            c (spin (iv/get-new (track s)))
            keep (v2/observe! c (fn [_ _]))
            r (comb/race c (v2/deferred))
            seen (atom [])]
        (v2/value-async r (fn [v err?] (assert (not err?)) (swap! seen conj v)))
        (v2/write! s :changed)
        (v2/value-async r (fn [v err?] (assert (not err?)) (swap! seen conj v)))
        (assert (= [:first :first] @seen))
        (keep))
      (let [ready (v2/deferred)
            trigger (v2/deferred)
            bad (task (await trigger) (throw (ex-info "first error" {:first true})))
            r (comb/race bad ready)
            seen (atom [])]
        (v2/value-async r (fn [v err?] (swap! seen conj [(:first (ex-data v)) err?])))
        (v2/deliver! trigger :fail)
        (v2/deliver! ready :late)
        (assert (= [[true true]] @seen)))
      (let [winner (v2/deferred) finish (v2/deferred)
            shared (task (await finish))
            r (comb/race winner shared)
            seen (atom [])]
        (v2/deliver! winner :winner)
        (v2/deliver! finish :shared)
        (v2/value-async r (fn [v err?] (assert (not err?)) (swap! seen conj v)))
        (v2/value-async shared (fn [v err?] (assert (not err?)) (swap! seen conj v)))
        (assert (= [:winner :shared] @seen)))
      (let [x (v2/signal 1)
            a (spin (* 10 (iv/get-new (track x))))
            b (spin (+ 1 (await a)))
            d (v2/deferred)
            mb (v2/mailbox)
            t (task (let [[p q] (await-all [b d])] (+ p q (take! mb))))
            _ (v2/observe! b (fn [v _] (swap! out conj [:b v])))]
        (v2/write! x 2)
        (v2/deliver! d 100)
        (v2/post! mb 1000)
        (v2/value-async t (fn [v err?] (swap! out conj [:t v err?])))
        (js/setTimeout
         (fn []
           (let [expected [[:b 11] [:b 21] [:t 1111 false]]]
             (println "observed" @out)
             (if (= expected @out)
               (println "SMOKE OK")
               (do (println "SMOKE FAIL, expected" expected) (js/process.exit 1)))))
         50)))))

(set! *main-cli-fn* -main)
