(ns org.replikativ.spindel.v2.sci.surface-test
  "What SCI code can reach: the v2 body surface by name, no engine internal,
   no world. Ports sci/{lock,context,boundary,trampoline}_test."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2]
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
