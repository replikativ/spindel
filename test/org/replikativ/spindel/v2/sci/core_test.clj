(ns org.replikativ.spindel.v2.sci.core-test
  "v2 bodies written in SCI behave as the host macros' (§7): effects across
   slices, loop/recur across effects, try/catch/finally across suspensions,
   bindings that span effects, cancellation, scopes. Ports
   sci/{await_boundary,trampoline}_test."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.sci.support :as s :refer [checked ev v outcome]]))

(deftest a-task-awaits-across-slices
  (checked
   (let [w (s/vworld) ctx (s/interpreter)]
     (is (= 42 (v (ev w ctx "(task (let [a (task 20) b (spin 22)] (+ (await a) (await b))))"))))
     (is (= [:slept 3] (v (ev w ctx "(task (sleep 2) (let [x (await (task (sleep 1) 3))] [:slept x]))"))))
     (is (= 7 (ev w ctx "@(task 7)")) "a top-level deref is a host wait")
     (v2/release-world! w))))

(deftest loop-recur-across-effects-trampolines
  (checked
   (let [w (s/vworld) ctx (s/interpreter)]
     (is (= 45 (v (ev w ctx "(task (loop [i 0 acc 0] (if (< i 10) (recur (inc i) (+ acc (await (task i)))) acc)))"))))
     (testing "a long loop over settled debtors resumes in place without growing the stack"
       (is (= 20000 (v (ev w ctx "(let [one (task 1)]
                                   (task (loop [i 0 acc 0] (if (< i 20000) (recur (inc i) (+ acc (await one))) acc))))")))))
     (v2/release-world! w))))

(deftest a-throw-after-a-suspension-is-caught
  ;; the engine's catch-after-resume rule (catch_resume_test) holds for SCI code
  (checked
   (let [w (s/vworld) ctx (s/interpreter)
         run (fn [src] (v (ev w ctx (str "(defn boom [t] (throw (ex-info (name t) {:tag t}))) " src))))]
     (testing "after a sleep, after an await"
       (is (= [:caught :a] (run "(task (try (sleep 1) (boom :a) (catch Exception e [:caught (:tag (ex-data e))])))")))
       (is (= [:caught :b] (run "(task (try (await (task 1)) (boom :b) (catch Exception e [:caught (:tag (ex-data e))])))"))))
     (testing "a computation"
       (is (= [:caught :c] (run "(spin (try (sleep 1) (boom :c) (catch Exception e [:caught (:tag (ex-data e))])))"))))
     (testing "a throw after the inner region goes to the outer handler"
       (is (= [:outer :e] (run "(task (try (do (try (sleep 1) 1 (catch Exception _ :inner)) (sleep 1) (boom :e))
                                         (catch Exception e [:outer (:tag (ex-data e))])))"))))
     (testing "finally runs once, on return and on throw"
       (is (= [:v 1] (ev w ctx "(def fin (atom 0)) [@(task (try (sleep 1) :v (finally (swap! fin inc)))) @fin]")))
       (is (= [[:failed :f] 1]
              (ev w ctx "(def fin (atom 0))
                         [(try @(task (try (sleep 1) (throw (ex-info \"f\" {:tag :f})) (finally (swap! fin inc))))
                               (catch Exception e [:failed (:tag (ex-data e))]))
                          @fin]"))))
     (v2/release-world! w))))

(deftest a-finalizer-may-not-suspend
  ;; B8 holds for SCI code: the try region registered with the run
  (checked
   (let [w (s/vworld) ctx (s/interpreter)
         t (ev w ctx "(task (try 1 (finally (sleep 1))))")]
     (is (= :finalizer (:spindel/invalid (second (outcome t)))))
     (v2/release-world! w))))

(deftest a-binding-spans-effects-on-any-thread
  ;; B10 for SCI bindings: a run starts from its creator's SCI frame; a
  ;; `binding` spanning an effect holds after it, whichever thread resumes
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         ctx (s/interpreter {:bindings {'d d}})
         _ (ev w ctx "(def ^:dynamic *x* :root)")
         inner (ev w ctx "(task (binding [*x* :inner] (let [a *x*] (await d) [a *x*])))")
         exits (ev w ctx "(binding [*x* :creator] (task (let [a (binding [*x* :inner] (await d) *x*)] [a *x*])))")]
     (Thread/sleep 30)
     (is (= :future @(future (v2/deliver! d :go) :future)) "resumed from another thread")
     (is (= [:inner :inner] (v inner)))
     (is (= [:inner :creator] (v exits)) "the binding exits to the creator's frame")
     (is (= :root (ev w ctx "*x*")) "nothing leaks into the interpreter's root")
     (v2/release-world! w))))

(deftest cancelling-an-sci-task-runs-its-finalizers
  ;; port of sci-await-registers-and-cancels-in-the-owning-spin
  (checked
   (let [w (s/vworld)
         gate (binding [v2/*world* w] (v2/deferred))
         ctx (s/interpreter {:bindings {'gate gate}})
         t (ev w ctx "(def cleaned (atom [])) (task (try (await gate) (finally (swap! cleaned conj :cleaned))))")]
     (Thread/sleep 20)
     (v2/cancel-task! t)
     (is (v2/cancelled? (try (v2/value t 2000 ::timeout) (catch Exception e e))))
     (is (= [:cleaned] (ev w ctx "@cleaned")) "the SCI finally ran once")
     (testing "the creating run owns its child tasks"
       (let [p (ev w ctx "(def child-cleaned (atom 0))
                          (task (let [c (task (try (await gate) (finally (swap! child-cleaned inc))))]
                                  (await c)))")]
         (Thread/sleep 20)
         (v2/cancel-task! p)
         (is (s/wait-until #(= 1 (ev w ctx "@child-cleaned"))) "cancelling the parent cancels the child")))
     (v2/release-world! w))))

(deftest with-scope-cancels-what-it-still-owns
  (checked
   (let [w (s/vworld)
         gate (binding [v2/*world* w] (v2/deferred))
         ctx (s/interpreter {:bindings {'gate gate}})]
     (is (= :done (ev w ctx "(def n (atom 0))
                             @(task (with-scope (task (try (await gate) (finally (swap! n inc)))) (sleep 1) :done))")))
     (is (s/wait-until #(= 1 (ev w ctx "@n"))) "the scope's task was cancelled; its finally ran")
     (v2/release-world! w))))

(deftest a-computation-reruns-from-sci
  (checked
   (let [w (s/vworld)
         x (binding [v2/*world* w] (v2/signal 1))
         ctx (s/interpreter {:bindings {'x x}})
         c (ev w ctx "(spin (* 2 (:new (track x))))")]
     (is (= 2 (v c)))
     (binding [v2/*world* w] (v2/write! x 5))
     (is (= 10 (v c)))
     (v2/release-world! w))))

(deftest an-aseq-from-sci
  (checked
   (let [w (s/vworld) ctx (s/interpreter)]
     (is (= [0 10 20]
            (v (ev w ctx "(let [k 10
                                xs (aseq [[n] [0]] (when (< n 3) (sleep 1) [(* k n) [(inc n)]]))]
                            (task (loop [p xs acc []] (if-let [[x nx] (await p)] (recur nx (conj acc x)) acc))))"))))
     (v2/release-world! w))))

(deftest a-fork-local-task-from-sci
  (checked
   (let [w (s/vworld) ctx (s/interpreter)
         t (ev w ctx "(task-with {:fork-local true} (sleep 1000))")]
     (is (v2/fork-local? t))
     (v2/release-world! w))))

(deftest old-names-are-aliases-only-when-asked
  (let [src "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                      '[org.replikativ.spindel.effects.await :refer [await]])
             @(spin (inc (await (spin 41))))"]
    (checked
     (let [w (s/vworld)]
       (is (thrown? Exception (ev w (s/interpreter) src)) "not installed by default")
       (is (= 42 (ev w (s/interpreter {} {:old-names :task}) src)) "spin as task")
       (is (= 42 (ev w (s/interpreter {} {:old-names :spin}) src)) "spin as computation")
       (is (= :invalid (try (s/interpreter {} {:old-names :yes}) (catch Exception _ :invalid))))
       (v2/release-world! w)))))
