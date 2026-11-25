(ns org.replikativ.spindel.v2.dom.addressing-fixture
  "A static element tree for D2 (phase-d design §2.10): its addresses are
   pinned as literals in addressing-cljc-test, so they must be the same on
   the JVM and on Node. The addresses hash the source locations below:
   moving a form changes them, and the literals must be regenerated."
  (:require [org.replikativ.spindel.v2.dom.elements :as el]))

(defn card [x]
  (el/li {:class "card"} (el/span x)))

(defn tree []
  (el/div {:class "root"}
          (el/span "a")
          (el/ul (el/li {:key "k"} "x")
                 (el/li "y")
                 (card "c"))))
