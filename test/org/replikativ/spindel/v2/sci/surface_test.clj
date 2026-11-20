(ns org.replikativ.spindel.v2.sci.surface-test
  "What SCI code can reach: the v2 body surface by name, no engine internal,
   no world. Ports sci/{lock,context,boundary,trampoline}_test."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.sci :as v2sci]
            [org.replikativ.spindel.v2.sci.support :as s :refer [checked ev v]]
            [sci.core :as sci]))

(deftest the-surface-is-pinned
  ;; a new public is reviewed before sandbox code reaches it
  (let [w (s/vworld) ctx (s/interpreter)]
    (is (= '#{spin task task-with aseq with-scope with-path
              track await await-all await-any take! acquire! offload external await-op sleep savepoint}
           (set (keys (ev w ctx "(ns-publics 'org.replikativ.spindel.v2.core)")))))
    (is (= '#{->thunk thunk? force-thunk scope-continuation}
           (set (keys (ev w ctx "(ns-publics 'is.simm.partial-cps.runtime)")))))
    (v2/release-world! w)))

(deftest engine-internals-are-not-requirable
  (let [w (s/vworld) ctx (s/interpreter)]
    (doseq [sym ['spawn! 'create-comp! 'await-effect! 'custom-effect! 'enter-finally! 'open-scope!
                 'row-of 'cw 'active-run 'current-world '*world* 'world 'fork! 'fork 'in-world
                 'release-world! 'register-effect! 'defeffect 'body* 'empty-inputs]]
      (is (nil? (ev w ctx (str "(resolve 'org.replikativ.spindel.v2.core/" sym ")"))) (str sym)))
    (doseq [n ['org.replikativ.spindel.v2.rows 'org.replikativ.spindel.v2.sci
               'org.replikativ.spindel.v2.host 'org.replikativ.spindel.v2.savepoint]]
      (is (thrown? Exception (ev w ctx (str "(require '" n ")"))) (str n)))
    (doseq [sym ['enter-trampoline! 'leave-trampoline! '*scope-frame* 'bound-fn]]
      (is (thrown? Exception (ev w ctx (str "is.simm.partial-cps.runtime/" sym))) (str sym)))
    (v2/release-world! w)))

(deftest the-functions-an-expansion-calls-hand-out-no-engine-object
  ;; macroexpand shows the spliced host functions; each acts on the calling
  ;; run only and returns no row, scope or world
  (checked
   (let [w (s/vworld) ctx (s/interpreter)]
     (ev w ctx "(def ex (macroexpand-1 '(org.replikativ.spindel.v2.core/with-scope :x)))
                (def open-scope (first (second (second ex))))")
     (is (fn? (ev w ctx "open-scope")))
     (is (thrown? Exception (ev w ctx "(open-scope)")) "outside a body")
     (is (= :refused (v (ev w ctx "(task (let [s (open-scope)] (try (aget s 0) (catch Exception _ :refused))))")))
         "a scope is an opaque value")
     (testing "the spawn function makes an ordinary task"
       (ev w ctx "(def spawn (first (macroexpand-1 '(task 1))))")
       (is (= 5 (v (ev w ctx "(spawn 1 [] (fn [ok _] (ok 5)))")))))
     (v2/release-world! w))))

(deftest no-world-is-reachable
  ;; port of an-explicit-handle-keeps-its-world-to-itself and
  ;; host-vars-are-out-of-reach: interop is gated to the class allowlist
  (let [w (s/vworld) ctx (s/interpreter)
        h (ev w ctx "(def h (task 7)) h")]
    (is (v2/handle? h))
    (doseq [src ["(.-w h)" "(.w h)" "(.-cell h)"]]
      (is (thrown-with-msg? Exception #"not allowed|Unable to resolve" (ev w ctx src)) src))
    (doseq [src ["(clojure.lang.Var/getThreadBindings)" "(.getClassLoader (class 1))"
                 "(-> \"x\" .getClass .getClassLoader (.loadClass \"java.lang.Runtime\"))"]]
      (is (thrown? Exception (ev w ctx src)) src))
    (is (= 7 (ev w ctx "@h")) "the handle still works")
    (v2/release-world! w)))

(deftest region-functions-cannot-unbalance-a-run
  ;; the spliced finally functions are reachable through macroexpand; an
  ;; unbalanced call changes nothing, so the run still retires
  (checked
   (let [w (s/vworld) ctx (s/interpreter)]
     (ev w ctx "(def ex (macroexpand-1 '(org.replikativ.spindel.v2.core/with-scope :x)))
                (def enter (first (second (second (nth ex 2)))))
                (def fin (nth (nth ex 2) 2))
                (def exit (first (second fin)))
                (def leave (first (second (nth (nth fin 2) 2))))")
     (is (= [:entered :exited :left]
            [(v (ev w ctx "(task (enter) (enter) :entered)"))
             (v (ev w ctx "(task (exit) (exit) :exited)"))
             (v (ev w ctx "(task (leave) :left)"))]))
     (is (= :outside (ev w ctx "(enter) (exit) (leave) :outside")) "outside a body they do nothing")
     (v2/release-world! w)
     (is (not= ::timeout (v2/await-complete w 2000 ::timeout)) "every run retired: the world completes"))))

(def ^:private scope-fns
  "(def ex (macroexpand-1 '(org.replikativ.spindel.v2.core/with-scope :x)))
   (def open-scope (first (second (second ex))))
   (def close-scope (first (second (nth (nth (nth ex 2) 2) 2))))
   (def stash (atom nil)) (def log (atom []))")

(def ^:private opener
  "(task (let [s (open-scope)]
           (reset! stash s)
           (task (try (await gate) :child-done (finally (swap! log conj :child-finally))))
           (await gate)
           :a-done))")

(deftest a-scope-closes-only-in-the-run-that-opened-it
  ;; a scope handed out by the spliced open-scope is bound to its run: another
  ;; run, or a run of an unrelated world, closing it changes nothing
  (checked
   (let [w1 (s/vworld) w2 (s/vworld)
         gate (binding [v2/*world* w1] (v2/deferred))
         ctx (s/interpreter {:bindings {'gate gate}})]
     (ev w1 ctx scope-fns)
     (let [a (ev w1 ctx opener)]
       (is (s/wait-until #(some? (ev w1 ctx "@stash"))))
       (testing "another run of the same world"
         (is (= :b-closed (v (ev w1 ctx "(task (close-scope @stash) :b-closed)"))))
         (is (= [] (ev w1 ctx "@log")) "the scope's task was not cancelled"))
       (testing "a run of an unrelated world"
         (is (= :c-closed (v (ev w2 ctx "(task (close-scope @stash) :c-closed)"))))
         (is (= [] (ev w1 ctx "@log"))))
       (v2/deliver! gate 1)
       (is (= :a-done (v a)))
       (is (= [:child-finally] (ev w1 ctx "@log")) "the opener's own close still cancels at its exit"))
     (v2/release-world! w1)
     (v2/release-world! w2))))

(deftest an-inherited-scope-closes-in-the-fork
  ;; the same run in a fork that inherited the scope may close it there
  (checked
   (let [w (s/vworld)
         [gate d] (binding [v2/*world* w] [(v2/deferred) (v2/deferred)])
         p (s/interpreter {:bindings {'gate gate 'd d}})
         registry (atom {w p})
         _ (v2sci/set-resolver! p (fn [w _] (get @registry w)))
         t (ev w p "(def log (atom []))
                    (task (with-scope (task (try (await gate) (finally (swap! log conj :cancelled))))
                                      (await d)
                                      :closed))")
         child (v2/fork! w)
         c (sci/fork p)]
     (swap! registry assoc child c)
     (v2/deliver! (v2/in-world child d) 1)
     (is (= :closed (v (v2/in-world child t))))
     (is (s/wait-until #(= [:cancelled] (sci/eval-string* c "@log"))) "the fork's scope task was cancelled")
     (is (= [] (sci/eval-string* p "@log")) "the parent's scope is still open")
     (v2/deliver! d 1)
     (is (= :closed (v t)))
     (v2/release-world! child)
     (v2/release-world! w))))
