(ns org.replikativ.spindel.v2.running-clause-test
  "§2, B3, T11: a dep edge registered inside a running finally clause is not
   re-entrant. An invalidation there restarts the body; before, T11 resumed
   the new run inside a clause it never entered (B8 bypassed, an orphan
   finally-leave)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await]]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)

(defn- vworld [] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook *divergences*))}))

(defmacro ^:private checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 400) false :else (do (Thread/sleep 5) (recur (inc n))))))

(defn balanced-finally?
  "Every run's accepted finally items in `log` follow the model's stack: an
   exit needs an open region on top, a leave a running clause."
  [log]
  (let [step (fn [st tag]
               (case tag
                 :finally-enter (conj st :open)
                 :finally-exit (when (= :open (peek st)) (conj (pop st) :running))
                 :finally-leave (when (= :running (peek st)) (pop st))))
        stacks (reduce (fn [acc {[tag r] :item ok :accepted}]
                         (if (and ok (#{:finally-enter :finally-exit :finally-leave} tag))
                           ;; a run once broken stays nil
                           (assoc acc r (some-> (get acc r []) (step tag)))
                           acc))
                       {} log)]
    (not-any? nil? (vals stacks))))

(deftest a-track-in-a-running-clause-restarts-the-body
  ;; the clause tracks `s`; at 1 it awaits an unresolved deferred, which a
  ;; finally clause may not (B8). The rerun starts from the body, enters the
  ;; clause itself and is refused there
  (checked
   (let [w (vworld)
         log (atom [])]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             d (v2/deferred)
             c (spin (try (swap! log conj :body)
                          :v
                          (finally
                            (let [x (iv/get-new (track s))]
                              (swap! log conj [:fin x])
                              (when (= 1 x) (swap! log conj [:awaited (await d)]))))))
             seen (atom [])]
         (v2/observe! c (fn [v err?] (swap! seen conj [(if err? (:spindel/invalid (ex-data v)) v) err?])))
         (v2/write! s 1)
         (is (wait-until #(= [[:v false] [:finalizer true]] @seen)) "the rerun's await in the clause is refused")
         (v2/deliver! d :late)
         (is (= [:body [:fin 0] :body [:fin 1]] @log) "the rerun started from the body")))
     (is (balanced-finally? (verify/log w)))
     (v2/release-world! w)
     (is (true? (v2/await-complete w 5000 ::timeout))))))

(deftest an-await-in-a-running-clause-restarts-the-body
  ;; the clause awaits a live computation (no suspension); its change
  ;; invalidates `c` at that site
  (checked
   (let [w (vworld)
         log (atom [])]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             inner (spin (iv/get-new (track s)))
             _ (v2/observe! inner (fn [_ _]))
             c (spin (try (swap! log conj :body)
                          :v
                          (finally (swap! log conj [:fin (await inner)]))))
             seen (atom [])]
         (v2/observe! c (fn [v err?] (swap! seen conj [v err?])))
         (is (wait-until #(= [[:v false]] @seen)))
         (v2/write! s 1)
         (is (wait-until #(= [:body [:fin 0] :body [:fin 1]] @log)) "the rerun started from the body")))
     (is (balanced-finally? (verify/log w)))
     (v2/release-world! w)
     (is (true? (v2/await-complete w 5000 ::timeout))))))

(deftest a-leave-without-a-running-clause-is-refused
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [t (task (v2/leave-finalizer!) :unreached)]
         (is (= :finally-leave (try (v2/value t 2000 ::timeout)
                                    (catch clojure.lang.ExceptionInfo e (:spindel/invalid (ex-data e))))))
         (is (some #(and (= :finally-leave (first (:item %))) (false? (:accepted %))) (verify/log w))
             "a refused log entry")))
     (v2/release-world! w))))
