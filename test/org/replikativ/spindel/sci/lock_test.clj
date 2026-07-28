(ns org.replikativ.spindel.sci.lock-test
  "Security regression tests for the locked-by-default SCI context.

  `spindel.sci.core/common-classes` used to carry `:allow :all`, which turns
  SCI's per-class interop gate OFF (ADR 0015). A spindel-backed sandbox running
  code an outsider can influence could then reach an arbitrary host method off
  ANY object — `.getClass` → `.getClassLoader` → `.loadClass \"java.lang.Runtime\"`
  → reflect → host shell. Removing `:allow :all` makes interop fall back to the
  per-class allowlist, so unregistered instance interop is denied.

  These two tests pin both directions:
  - a real spin (let + await, suspend/resume through the Thunk trampoline) still
    works with interop locked — the registered classes are enough, and
  - interop on an UNregistered class (java.lang.Class) is denied, i.e. the
    escape path is closed at the spindel layer, not only in downstream sandboxes.

  Requires SCI >= 0.14 (ADR 0007 instance-member control) for the deny direction;
  the :test alias pins a version new enough to exercise it."
  (:require [clojure.test :refer [deftest is testing]]
            [sci.core :as sci]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.sci.macro :as macro]))

(deftest spin-runs-with-interop-locked
  (testing "a real spin (let + await) evaluates under the lock — the engine needs
            no `:allow :all`, only the registered classes"
    (let [rt (ctx/create-execution-context)]
      (try
        (let [sci-ctx (macro/create-spin-macro-context {:runtime rt})]
          (binding [ec/*execution-context* rt]
            ;; let + await suspends and resumes through the Thunk trampoline (interop
            ;; on the registered is.simm.partial_cps.runtime.Thunk / Spin classes),
            ;; so a correct result proves the CPS machinery works with `:allow :all`
            ;; gone. (A `loop`/`recur` ACROSS an await is deliberately not asserted
            ;; here — that SCI path hangs regardless of `:allow :all`, i.e. it is a
            ;; pre-existing engine limitation orthogonal to interop locking.)
            (is (= 30
                   (macro/eval-and-deref sci-ctx
                     "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                               '[org.replikativ.spindel.effects.await :refer [await]])
                      (spin
                        (let [a (spin 10)
                              b (spin 20)
                              x (await a)
                              y (await b)]
                          (+ x y)))")))))
        (finally
          (ctx/stop-context! rt))))))

(deftest unregistered-instance-interop-is-denied
  (testing "with `:allow :all` gone, reflecting off an unregistered class throws —
            the getClassLoader→loadClass→Runtime escape is closed"
    (let [rt (ctx/create-execution-context)]
      (try
        (let [sci-ctx (macro/create-spin-macro-context {:runtime rt})]
          (binding [ec/*execution-context* rt]
            ;; java.lang.Class is NOT in common-classes, so an instance method on
            ;; it must be refused. This is the first hop of the reflection escape.
            (is (thrown-with-msg?
                 Exception #"(?i)not allowed"
                 (sci/eval-string* sci-ctx
                   "(.getClassLoader (class 1))")))
            ;; The concrete escape a sandboxed attacker would try.
            (is (thrown-with-msg?
                 Exception #"(?i)not allowed"
                 (sci/eval-string* sci-ctx
                   "(-> \"x\" .getClass .getClassLoader
                        (.loadClass \"java.lang.Runtime\"))")))))
        (finally
          (ctx/stop-context! rt))))))
