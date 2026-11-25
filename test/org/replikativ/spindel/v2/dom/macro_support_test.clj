(ns org.replikativ.spindel.v2.dom.macro-support-test
  "The trusted scope annotations of the macro-time walk (sol's P4a review,
   item 6) and the portable source identity of element addresses (item 5)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [await]]
            [org.replikativ.spindel.v2.macro-support :as ms]
            [org.replikativ.spindel.v2.dom.addressing :as addr]))

(defmacro ^{::ms/scope ::ms/transparent} passing [x] x)
(defmacro ^{::ms/scope ::ms/transparent} waiting [x] `(await ~x))   ; breaks the contract
(defmacro ^{::ms/scope ::ms/opaque} hiding [x] `(do ~x))             ; breaks the contract
(defmacro unannotated-waiting [x] `(await ~x))

(deftest scope-annotations-are-trusted-assertions
  (binding [*ns* (the-ns 'org.replikativ.spindel.v2.dom.macro-support-test)]
    (testing "honoured"
      (is (v2/effectful? {} '(passing (await x))) "a transparent macro's operands are walked")
      (is (v2/effectful? {} '(unannotated-waiting x)) "an unannotated macro is expanded"))
    (testing "not verified: a macro that breaks the contract misleads the walk"
      (is (not (v2/effectful? {} '(waiting x))) "an effect its transparent expansion adds is not seen")
      (is (not (v2/effectful? {} '(hiding (await x)))) "an opaque macro hides its operands"))))

(deftest canonical-source-paths
  (let [roots ["/w/src" "/w/test" "/w"]]
    (is (= "org/a/b.cljc" (addr/canonical-source "org/a/b.cljc" "/w" roots)) "a resource path (shadow-cljs, JVM require)")
    (is (= "org/a/b.cljc" (addr/canonical-source "src/org/a/b.cljc" "/w" roots)) "relative to the working directory")
    (is (= "org/a/b.cljc" (addr/canonical-source "/w/test/org/a/b.cljc" "/w" roots)) "absolute")
    (is (= "org/a/b.cljc" (addr/canonical-source "/checkout/test/org/a/b.cljc" "/checkout" ["/checkout/test" "/checkout/src"]))
        "another checkout")
    (is (= "org/a/b.cljc" (addr/canonical-source "file:/w/src/org/a/b.cljc" "/w" roots)) "a file URL")
    (is (= "org/a/b.cljc" (addr/canonical-source "jar:file:/m2/x.jar!/org/a/b.cljc" "/w" roots)) "inside a jar")
    (is (= "NO_SOURCE_PATH" (addr/canonical-source "NO_SOURCE_PATH" "/w" ["/w/src"])) "no file")
    (is (= "/elsewhere/b.cljc" (addr/canonical-source "/elsewhere/b.cljc" "/w" roots)) "outside every root: unchanged")))
