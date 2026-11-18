(ns org.replikativ.spindel.v2.catch-resume-test
  "A `try` in a body catches what the body throws after a suspension, exactly
   as it does before one: the resumed code's throws go to the handler that
   was in scope at the suspension, and to no inner one after its region ends."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await]]
            [org.replikativ.spindel.v2.verify :as verify]))

(def ^:dynamic *divergences* nil)
(defn- vworld [] (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))
(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- boom [tag] (throw (ex-info (name tag) {:tag tag})))

(defn- run1
  "The value of the handle `(f)` makes in `w`, or [:failed tag] when it fails."
  [w f]
  (try (v2/value (binding [v2/*world* w] (f)) 5000 ::timeout)
       (catch clojure.lang.ExceptionInfo e [:failed (:tag (ex-data e))])))

(deftest a-throw-after-a-suspension-is-caught
  (checked
   (let [w (vworld)]
     (testing "task, after a sleep"
       (is (= [:caught :a] (run1 w #(task (try (v2/sleep 1) (boom :a)
                                               (catch Exception e [:caught (:tag (ex-data e))])))))))
     (testing "task, after awaiting a task"
       (is (= [:caught :b] (run1 w #(task (try (await (task 1)) (boom :b)
                                               (catch Exception e [:caught (:tag (ex-data e))])))))))
     (testing "computation, after a sleep"
       (is (= [:caught :c] (run1 w #(spin (try (v2/sleep 1) (boom :c)
                                               (catch Exception e [:caught (:tag (ex-data e))])))))))
     (testing "the value awaited is in scope"
       (is (= [:caught :d 7] (run1 w #(task (try (let [x (await (task 7))] (boom :d) x)
                                                 (catch Exception e [:caught (:tag (ex-data e)) 7])))))))
     (v2/release-world! w))))

(deftest a-handler-catches-only-its-own-region
  (checked
   (let [w (vworld)]
     (testing "a throw after the try's region goes to the outer handler"
       (is (= [:outer :e] (run1 w #(task (try (do (try (v2/sleep 1) 1 (catch Exception _ :inner))
                                                  (v2/sleep 1)
                                                  (boom :e))
                                              (catch Exception e [:outer (:tag (ex-data e))])))))))
     (testing "the same, with no suspension after the inner try"
       (is (= [:outer :f] (run1 w #(task (try (do (try (v2/sleep 1) 1 (catch Exception _ :inner))
                                                  (boom :f))
                                              (catch Exception e [:outer (:tag (ex-data e))])))))))
     (testing "a catch body that throws after a suspension reaches the outer handler"
       (is (= [:outer :g] (run1 w #(task (try (try (v2/sleep 1) (boom :x)
                                                   (catch Exception _ (v2/sleep 1) (boom :g)))
                                              (catch Exception e [:outer (:tag (ex-data e))])))))))
     (testing "a class that does not match propagates; finally runs once"
       (let [fins (atom 0)]
         (is (= [:outer :h]
                (run1 w #(task (try (try (v2/sleep 1) (boom :h)
                                         (catch ArithmeticException _ :wrong)
                                         (finally (swap! fins inc)))
                                    (catch Exception e [:outer (:tag (ex-data e))]))))))
         (is (= 1 @fins))))
     (testing "uncaught, the task fails with it"
       (is (= [:failed :i] (run1 w #(task (v2/sleep 1) (boom :i))))))
     (testing "in a loop after recur"
       (is (= [:caught :j 3]
              (run1 w #(task (try (loop [i 0]
                                    (v2/sleep 1)
                                    (if (= i 3) (boom :j) (recur (inc i))))
                                  (catch Exception e [:caught (:tag (ex-data e)) 3])))))))
     (v2/release-world! w))))
