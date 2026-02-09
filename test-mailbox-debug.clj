(require '[org.replikativ.spindel.engine.core :as ec])
(require '[org.replikativ.spindel.engine.context :as ctx])
(require '[org.replikativ.spindel.engine.impl.atoms])
(require '[org.replikativ.spindel.spin.sync :as sync])
(require '[org.replikativ.spindel.spin.cps :refer [spin]])
(require '[org.replikativ.spindel.effects.await :refer [await]])

(println "=== Mailbox Debug Test ===")

(binding [ec/*execution-context* (ctx/create-execution-context)]
  (let [mbx (sync/mailbox)]
    (println "1. Created mailbox")

    ;; Post three messages
    (mbx :first)
    (println "2. Posted :first")
    (mbx :second)
    (println "3. Posted :second")
    (mbx :third)
    (println "4. Posted :third")

    ;; Consume them one at a time
    (println "5. Consuming...")
    (let [msg1 @(spin (await mbx))]
      (println "   Got:" msg1))
    (let [msg2 @(spin (await mbx))]
      (println "   Got:" msg2))
    (let [msg3 @(spin (await mbx))]
      (println "   Got:" msg3))

    (println "6. All consumed!")))

(println "=== Done ===")
