(ns org.replikativ.spindel.v2.savepoint-test
  "§8.2 savepoints: publish, in-place resume, instantiate/activate, abandon."
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

(defn- outcome [w h]
  (try [:ok (v2/value (v2/in-world w h) 1000 ::timeout)] (catch Exception e [:err (ex-data e)])))

(deftest no-handler-is-identity
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [t (task (inc (v2/savepoint :site 41)))]
         (is (= 42 (v2/value t 1000 ::timeout))))))))

(deftest handler-resumes-in-place
  (checked
   (let [w (vworld)]
     (v2/install-handlers! w {:site (fn [p] (v2/resume! p (* 10 (:payload p))))})
     (binding [v2/*world* w]
       (let [t (task (inc (v2/savepoint :site 4)))]
         (is (= 41 (v2/value t 1000 ::timeout))))))))

(deftest instantiate-particles
  (checked
   (let [w (vworld)
         pubs (atom [])]
     (v2/install-handlers! w {:choose (fn [p] (swap! pubs conj p))})
     (binding [v2/*world* w]
       (let [x (v2/signal 100)
             t (task (let [v (v2/savepoint :choose nil)]
                       (+ v (iv/get-new (track x)))))]
         (is (= ::pending (v2/value t 100 ::pending)) "parked at the savepoint")
         (let [p (first @pubs)
               worlds (mapv (fn [v] (doto (v2/instantiate p) (v2/activate! v))) [1 2 3])]
           (is (= [[:ok 101] [:ok 102] [:ok 103]] (mapv #(outcome % t) worlds)) "independent particles")
           (v2/abandon! p)
           (is (:spindel/cancelled (second (outcome w t))) "the source run is abandoned")))))))

(deftest other-pending-savepoints-fail-in-an-instance
  (checked
   (let [w (vworld)
         pubs (atom {})]
     (v2/install-handlers! w {:default (fn [p] (swap! pubs assoc (:payload p) p))})
     (binding [v2/*world* w]
       (let [a (task (try (v2/savepoint :s :a) (catch Exception e (if (:spindel/forked (ex-data e)) :forked (throw e)))))
             b (task (v2/savepoint :s :b))]
         (v2/value (v2/signal 0) 100 nil)
          ;; b's basis was taken while a was pending
         (let [i (doto (v2/instantiate (get @pubs :b)) (v2/activate! :went))]
           (is (= [:ok :went] (outcome i b)))
           (is (= [:ok :forked] (outcome i a)) "a has no publication in b's instance")))))))

(deftest resume-after-cancel-is-refused
  (checked
   (let [w (vworld)
         pubs (atom [])
         ran (atom false)]
     (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
     (binding [v2/*world* w]
       (let [t (task (do (v2/savepoint :s nil) (reset! ran true) :after))]
         (v2/value (v2/signal 0) 100 nil)
         (v2/cancel-task! t)
         (v2/resume! (first @pubs) 7)
         (v2/value (v2/signal 0) 100 nil)
         (is (false? @ran) "a cancelled run does not continue from its savepoint")
         (is (:spindel/cancelled (second (outcome w t)))))))))
