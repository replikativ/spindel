(ns org.replikativ.spindel.v2.site-path-test
  "§8.2 P1-P6: `with-path` labels effect sites with readable paths."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task spin with-path]]
            [org.replikativ.spindel.v2.savepoint :as sp]))

(v2/register-effect! `path-here (fn [_ ctx] [:value (:path ctx)]))
(defn path-here [] (throw (ex-info "path-here outside a body" {})))

(defmacro in-world [& body]
  `(let [w# (v2/world)]
     (try (binding [v2/*world* w#] ~@body)
          (finally (v2/release-world! w#)))))

(defn- run [t] (v2/value t 2000 ::timeout))

(deftest a-path-labels-the-sites-inside-it
  (in-world
   (is (= [nil [[:a] [:a :b 2] [:a]] nil]
          (run (task [(path-here)
                      (with-path [:a]
                        [(path-here)
                         (with-path [:b 2] (path-here))
                         (path-here)])
                      (path-here)])))
       "P1 nests, P2 restores at normal exit")
   (is (= [[:step 0] [:step 1] [:step 2]]
          (run (task (loop [i 0 ps []]
                       (if (= i 3) ps (recur (inc i) (conj ps (with-path [:step i] (path-here)))))))))
       "a loop index in the path")))

(deftest a-path-survives-suspension-and-is-restored-after-an-error
  (in-world
   (is (= [[:a] [:a] nil]
          (run (task [(with-path [:a] (path-here))
                      (with-path [:a] (v2/sleep 5) (path-here))
                      (do (try (with-path [:x] (throw (ex-info "boom" {})))
                               (catch Exception _ nil))
                          (path-here))]))))
   (is (= [:a]
          (run (task (with-path [:a]
                       (try (throw (ex-info "inner" {}))
                            (catch Exception _ (path-here)))))))
       "an error caught inside the path keeps it")))

(deftest created-tasks-and-computations-inherit-the-path
  (in-world
   (is (= [[:a] [:a :b] [:a]]
          (run (task (with-path [:a]
                       [(v2/await (task (path-here)))
                        (v2/await (task (with-path [:b] (path-here))))
                        (v2/await (spin (path-here)))])))))
   (is (= [:a]
          (run (task (let [t (with-path [:a] (task (v2/sleep 5) (path-here)))]
                       (v2/await t)))))
       "P3: a task keeps the path it was created under, whatever its creator does after")))

(deftest an-adopted-computation-takes-a-new-path
  ;; P4: the same creation under another path is re-run with it
  (in-world
   (let [p (v2/signal [:a])
         c (spin (let [label (v2/track p)]
                   (with-path (:new label) (v2/await (spin (path-here))))))]
     (is (= [:a] (v2/value c 2000 ::timeout)))
     (v2/write! p [:b])
     (is (= [:b] (loop [i 0]
                   (let [v (v2/value c 2000 ::timeout)]
                     (if (or (= [:b] v) (> i 100)) v (do (Thread/sleep 5) (recur (inc i)))))))))))

(deftest outside-a-body-the-path-is-ignored
  (is (= 3 (with-path [:a] (+ 1 2)))))

(deftest a-savepoint-instance-continues-with-its-path
  (in-world
   (let [w v2/*world* pubs (atom [])]
     (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
     (let [t (task (with-path [:a] (v2/savepoint :s nil) (path-here)))]
       (loop [i 0] (when (and (empty? @pubs) (< i 200)) (Thread/sleep 5) (recur (inc i))))
       (let [i (doto (v2/instantiate (first @pubs)) (v2/activate! nil))]
         (is (= [:a] (v2/value (v2/in-world i t) 2000 ::timeout)))
         (v2/resume! (first @pubs) nil)
         (is (= [:a] (run t)))
         (v2/release-world! i))))))

(deftest savepoint-addresses-start-with-the-path
  (let [frame [7] key 3]
    (is (= :x (sp/address :x {:frame frame :key key})))
    (is (= [[7] 3] (sp/address nil {:frame frame :key key})))
    (is (= [:step 1 :x] (sp/address :x {:frame frame :key key :path [:step 1]})))
    (is (= [:a :b 2 :y] (sp/address [:b 2 :y] {:frame frame :key key :path [:a]})))
    (is (= [:a [[7] 3]] (sp/address nil {:frame frame :key key :path [:a]})))))
