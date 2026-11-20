(ns org.replikativ.spindel.v2.sci.effects-test
  "Effects from SCI bodies: registered custom effects exposed by symbol (R3),
   and the built-in effects whose callbacks run SCI code on host threads
   (offload, external, await-op)."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.sci :as v2sci]
            [org.replikativ.spindel.v2.sci.support :as s :refer [checked ev v outcome]]
            [sci.core :as sci]))

(v2/register-effect! `twice (fn [[x] _] [:value (* 2 x)]))
(v2/register-effect! `park (fn [[h] _] [:await h]))
(v2/register-effect! `where (fn [_ ctx] [:value (select-keys ctx [:path :site])]))
(v2/register-effect! `later (fn [_ _] [:value :effect]))
(v2/register-effect! `unexposed (fn [_ _] [:value :leaked]))

(deftest custom-effects-from-sci
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         ctx (s/interpreter {:bindings {'d d}} {:effects {'fx/twice `twice 'fx/park `park}})]
     (is (= 42 (v (ev w ctx "(task (fx/twice 21))"))))
     (testing "an effect that suspends resumes the SCI body on its heap"
       (let [t (ev w ctx "(def seen (atom [])) (task (let [x (fx/park d)] (swap! seen conj x) @seen))")]
         (v2/deliver! d :delivered)
         (is (= [:delivered] (v t)))))
     (testing "the handler sees the site and with-path's path"
       (v2sci/expose-effect! ctx 'fx/where `where)
       (let [[a b c] (v (ev w ctx "(task [(fx/where) (with-path [:a 1] (fx/where)) (fx/where)])"))]
         (is (nil? (:path a)))
         (is (= [:a 1] (:path b)))
         (is (nil? (:path c)) "the path is restored when with-path exits")
         (is (= 3 (count (set (map :site [a b c])))) "each call site has its own site")))
     (testing "only exposed effects are reachable: no SCI name reaches another registered effect"
       (is (nil? (ev w ctx (str "(resolve '" `unexposed ")")))))
     (v2/release-world! w))))

(deftest bodies-compiled-before-exposure-do-not-see-the-effect
  ;; R3 (v2:5634): the breakpoint is fixed when the body is compiled
  (checked
   (let [w (s/vworld)
         ctx (s/interpreter {:namespaces {'fx {'later (fn [] :plain)}}})
         before (ev w ctx "(defn before [] (task (fx/later)))")]
     (v2sci/expose-effect! ctx 'fx/later `later)
     (is (some? before))
     (is (= :plain (v (ev w ctx "(before)"))) "compiled before: a plain call")
     (is (= :effect (v (ev w ctx "(task (fx/later))"))) "compiled after: the effect")
     (is (thrown? Exception (v2sci/expose-effect! ctx 'later `later)) "qualified symbols only")
     (v2/release-world! w))))

(deftest host-callbacks-run-in-the-interpreter
  ;; offload's f, external's f and its cancel fn, and await-op's op run on
  ;; host threads outside the slice; they see the interpreter's heap
  (checked
   (let [w (s/vworld) ctx (s/interpreter)]
     (ev w ctx "(def counter (atom 0))")
     (is (= 1 (v (ev w ctx "(task (offload (fn [] (swap! counter inc))))"))))
     (is (= 2 (v (ev w ctx "(task (offload (fn [] (swap! counter inc)) {}))"))))
     (is (= 8 (v (ev w ctx "(task (external (fn [complete!] (complete! (+ 5 (swap! counter inc))) nil)))"))))
     (is (= 13 (v (ev w ctx "(task (await-op (fn [ok _] (ok (+ 9 (swap! counter inc))))))"))))
     (testing "external's cancel fn runs when the task is cancelled"
       (let [t (ev w ctx "(def cancelled (atom false))
                          (task (external (fn [_] (fn [] (reset! cancelled true) :joined))))")]
         (Thread/sleep 20)
         (v2/cancel-task! t)
         (is (s/wait-until #(true? (ev w ctx "@cancelled"))))))
     (v2/release-world! w))))

(deftest group-and-consuming-effects-from-sci
  (checked
   (let [w (s/vworld)
         mb (binding [v2/*world* w] (v2/mailbox))
         ctx (s/interpreter {:bindings {'mb mb}})]
     (is (= [1 2] (v (ev w ctx "(task (await-all [(task 1) (task (sleep 1) 2)]))"))))
     (is (= :fast (v (ev w ctx "(task (await-any [(task (sleep 500) :slow) (task :fast)]))"))))
     (let [t (ev w ctx "(task [(take! mb) (take! mb)])")]
       (v2/post! mb :a)
       (v2/post! mb :b)
       (is (= [:a :b] (v t))))
     (is (= 5 (v (ev w ctx "(task (savepoint :site 5))"))) "a savepoint without a handler is the identity")
     (v2/release-world! w))))
