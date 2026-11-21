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

(defn- held-executor
  "An executor that runs nothing until `run-held!`."
  []
  (let [held (atom [])]
    [(reify java.util.concurrent.Executor (execute [_ r] (swap! held conj r)))
     (fn [] (let [[rs] (reset-vals! held [])] (run! #(.run ^Runnable %) rs)))]))

(deftest a-host-callback-runs-where-the-resolver-says-when-it-runs
  ;; offload's f and external's cancel fn resolve their interpreter when they
  ;; are called, as bodies and continuations do: after a staged replacement
  ;; they act on the staged heap, also when the replaced one is retired
  ;; (before, a retired one made the cancel fn throw: the resource never
  ;; joined and the world never completed)
  (doseq [retire? [false true]]
    (testing (str "replaced interpreter retired: " retire?)
      (checked
       (let [w (s/vworld)
             [ex run-held!] (held-executor)
             p (s/interpreter {:bindings {'ex ex}})
             registry (atom {w p})
             _ (v2sci/set-resolver! p (fn [world _] (get @registry world)))
             off (ev w p "(def n (atom 0)) (task (offload (fn [] (swap! n inc)) {:pool ex}))")
             ext (ev w p "(def cancelled (atom false))
                          (task (try (external (fn [_] (fn [] (reset! cancelled true) :joined)))
                                     (finally :cleanup)))")
             staged (sci/fork p)]
         (swap! registry assoc w staged)
         (when retire? (sci/retire! p))
         (run-held!)
         (is (= 1 (v off)) "offload's f ran on the staged heap")
         (is (= 1 (sci/eval-string* staged "@n")))
         (v2/cancel-task! ext)
         (is (v2/cancelled? (try (v2/value ext 2000 ::timeout) (catch Exception e e))))
         (is (true? (sci/eval-string* staged "@cancelled")) "the cancel fn ran on the staged heap")
         (when-not retire?
           (is (= [0 false] (sci/eval-string* p "[@n @cancelled]")) "the replaced heap is untouched"))
         (v2/release-world! w)
         (is (not= ::timeout (v2/await-complete w 2000 ::timeout)) "the cancelled run retired"))))))

(deftest a-refused-host-callback-runs-no-sci-code
  (testing "offload's f and await-op's op fail their effect with ::no-interpreter"
    (checked
     (let [w (s/vworld)
           p (s/interpreter)]
       ;; refuses calls outside a slice (executor threads), answers slices
       (v2sci/set-resolver! p (fn [_ ctx] (when (v2/active-run) ctx)))
       (ev w p "(def ran (atom 0))")
       (is (= [:caught ::v2sci/no-interpreter]
              (v (ev w p "(task (try (offload (fn [] (swap! ran inc))) (catch Exception e [:caught (:type (ex-data e))])))"))))
       (is (= [:caught ::v2sci/no-interpreter]
              (v (ev w p "(task (try (await-op (fn [ok _] (swap! ran inc) (ok 1))) (catch Exception e [:caught (:type (ex-data e))])))"))))
       (is (= 0 (sci/eval-string* p "@ran")) "neither ran SCI code")
       (v2/release-world! w))))
  (testing "a refused cancel fn counts as joined"
    (checked
     (let [w (s/vworld)
           p (s/interpreter)
           refuse? (atom false)
           _ (v2sci/set-resolver! p (fn [_ ctx] (when-not @refuse? ctx)))
           t (ev w p "(def cancelled (atom false))
                      (task (external (fn [_] (fn [] (reset! cancelled true) nil))))")]
       (reset! refuse? true)
       (v2/cancel-task! t)
       (is (some? (try (v2/value t 2000 ::timeout) (catch Exception e e))))
       (is (false? (sci/eval-string* p "@cancelled")) "the cancel fn did not run")
       (v2/release-world! w)
       (is (not= ::timeout (v2/await-complete w 2000 ::timeout)) "the resource joined; the world completed")))))
