(require '[is.simm.spindel.runtime.core :as rtc])
(require '[is.simm.spindel.runtime.context :as ctx])
(require '[is.simm.spindel.runtime.impl.atoms])
(require '[is.simm.spindel.spin.sync :as sync])
(require '[is.simm.spindel.spin.cps :refer [spin]])
(require '[is.simm.spindel.effects.await :refer [await]])

(println "=== Mailbox Debug Test ===")

(binding [rtc/*execution-context* (ctx/create-execution-context)]
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
