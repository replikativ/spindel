(ns org.replikativ.spindel.lifetime.custody-model-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.invariants :as inv]))

(def a [:w 0])
(def b [:w 10])
(def child [:w 1])
(def s0 [:scope :id 0])
(def k0 [:cap 0])
(def k1 [:cap 1])
(def external [:external :model-host])
(defn holder [w id] (m/execution-holder w id))
(defn independent-root [state w]
  (let [world (m/world-row w nil :root w)]
    (-> state (assoc-in [:worlds w] world) (update :registry conj w)
        (update :known-worlds conj w) (assoc-in [:lineages w] (:lineage world)))))
(defn checked [state action]
  (let [after (m/step state action)]
    (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
    (is (empty? (inv/custody-edge-errors {:before state :action action :after after})))
    after))
(defn walk [state actions] (reduce checked state actions))
(defn refuses [state action error]
  (let [result (m/attempt state action)]
    (is (= error (get-in result [:refusal :error])) (pr-str result))
    (is (= state (:state result)))))
(defn scope-fixture []
  (walk (independent-root (m/init-state {:external-principals #{external}}) b)
        [{:t :t12 :w a :scope s0 :parent [:root a]}
         {:t :t12 :w b :scope s0 :parent [:root b]}
         {:t :t19 :w a :v child :k k0 :scope s0}]))
(defn transfer [from to k successor op]
  {:t :t32 :k k :successor successor :op op :caller from :holder to :acceptor to})
(defn finish [state k]
  (let [c (m/cap state k) op (:op c)]
    (walk state [{:t :t27 :k k :op op :payload :payload :bases (:bases c) :steps []}
                 {:t :t29 :op op}])))

(deftest transfer-moves-cleanup-to-the-qualified-destination
  (let [initial (scope-fixture)
        moved (checked initial (transfer (holder a s0) (holder b s0) k0 k1 :move))
        old-closed (checked moved {:t :t13 :w a :scope s0})]
    (is (= (holder b s0) (:holder (m/cap old-closed k1))))
    (is (empty? (:queue (m/wr old-closed child))))
    (is (empty? (get-in old-closed [:custody :claims])))
    (is (nil? (m/ent old-closed b [:fork child])))
    (let [closed (checked old-closed {:t :t13 :w b :scope s0})
          envelope (first (:queue (m/wr closed child)))
          claim (get-in closed [:custody :claims (:custody-dispatch envelope)])]
      (is (= k1 (:cap claim)))
      (is (= (holder b s0) (:origin claim)))
      (is (nil? (get-in closed [:worlds b :scopes s0])))
      (is (= [:cleanup (:custody-dispatch envelope)] (:holder (m/cap closed k1))))
      (is (= closed (m/step closed {:t :t13 :w b :scope s0})))
      (let [sealed (checked closed {:t :queued :w child})
            done (finish sealed k1)]
        (is (= :discarded (:disposition (m/cap done k1))))
        (is (empty? (get-in done [:custody :by-holder])))
        (is (empty? (get-in done [:custody :claims])))))))

(deftest close-and-acceptance-serialize-before-dispatch
  (let [initial (scope-fixture)
        closed-source (checked initial {:t :t13 :w a :scope s0})]
    (refuses closed-source (transfer (holder a s0) (holder b s0) k0 k1 :late) ::m/stale-capability)
    (let [closed-destination (checked initial {:t :t13 :w b :scope s0})]
      (refuses closed-destination (transfer (holder a s0) (holder b s0) k0 k1 :late)
               ::m/invalid-destination))
    (let [moved (checked initial (transfer (holder a s0) (holder b s0) k0 k1 :move))
          closed (checked moved {:t :t13 :w b :scope s0})
          old-closed (checked closed {:t :t13 :w a :scope s0})]
      (is (= 1 (count (get-in old-closed [:custody :claims]))))
      (is (= 1 (count (:queue (m/wr old-closed child))))))))

(deftest partition-close-captures-only-the-retained-leaf
  (let [initial (scope-fixture)
        split (checked initial {:t :t33 :k k0 :op :split :caller (holder a s0)
                                :successors [{:k [:cap :a] :scope #{:a}} {:k [:cap :b] :scope #{:b}}]})
        moved (checked split (transfer (holder a s0) (holder b s0) [:cap :b] k1 :move))
        closed (checked moved {:t :t13 :w a :scope s0})
        sealed (checked closed {:t :queued :w child})
        done (finish sealed [:cap :a])]
    (is (= (holder b s0) (:holder (m/cap done k1))))
    (is (= :open (:disposition (m/cap done k1))))
    (is (not= :released (:status (m/wr done child))))
    (is (= #{k1} (get-in done [:custody :by-holder (holder b s0)])))))

(deftest authority-and-successor-validation-refuse-without-mutation
  (let [state (scope-fixture) action (transfer (holder a s0) (holder b s0) k0 k1 :move)]
    (refuses state (assoc action :caller (holder b s0)) ::m/stale-capability)
    (refuses state (assoc action :caller s0) ::m/stale-capability)
    (refuses state (assoc action :holder [:external :unregistered] :acceptor [:external :unregistered]) ::m/invalid-destination)
    (refuses state (dissoc action :acceptor) ::m/unaccepted-transfer)
    (refuses state (assoc action :successor k0) ::m/cap-id-reused)
    (refuses state {:t :t33 :k k0 :op :split :caller (holder a s0)
                    :successors [{:k k1 :scope #{:a}} {:k k1 :scope #{:b}}]} ::m/invalid-partition)
    (refuses state {:t :t33 :k k0 :op :split :caller (holder b s0)
                    :successors [{:k k1 :scope #{:a :b}}]} ::m/stale-capability)
    (let [moved (checked state action)]
      (refuses moved (transfer (holder b s0) external k1 k0 :revive) ::m/cap-id-reused))))

(deftest queued-disposal-authenticates-the-committed-claim
  (let [closed (checked (scope-fixture) {:t :t13 :w a :scope s0})
        event (first (:queue (m/wr closed child)))
        corrupt (assoc-in closed [:worlds child :queue 0 :cap] :other)]
    (is (seq (inv/custody-errors corrupt)))
    (refuses corrupt {:t :queued :w child} ::m/invalid-custody-claim)
    (let [sealed (checked closed {:t :queued :w child})
          duplicate (m/enqueue sealed child event)
          again (checked duplicate {:t :queued :w child})]
      (is (= (:op (m/cap sealed k0)) (:op (m/cap again k0))))
      (let [done (finish again k0)
            stale (m/enqueue done child event)]
        (is (= done stale))))))

(deftest close-preserves-already-committed-merge-and-recovery
  (doseq [outcome [nil :unknown :fail-permanent]]
    (let [initial (scope-fixture)
          sealed (checked initial {:t :t26 :caller (holder a s0) :k k0 :op :merge :kind :merge})
          prepared (if outcome
                     (walk sealed [{:t :t27 :k k0 :op :merge :payload :stable :bases (:bases (m/cap sealed k0))
                                    :steps [{:id 0 :kind :merge :system :a :recovery :query}]}
                                   {:t :t28 :op :merge :i 0 :outcome outcome :committed? (= :unknown outcome)}]) sealed)
          old-record (m/record prepared :merge)
          closed (checked prepared {:t :t13 :w a :scope s0})
          progressed (checked closed {:t :queued :w child})]
      (is (= :merge (:kind (m/cap progressed k0))))
      (is (= :merge (:op (m/cap progressed k0))))
      (is (= old-record (m/record progressed :merge)))
      (when (= :fail-permanent outcome)
        (is (= :incomplete (:disposition (m/cap progressed k0))))))))

(deftest restart-rebinds-every-durable-nonterminal-without-rewriting-merge
  (doseq [prepared? [false true]]
    (let [sealed (checked (scope-fixture) {:t :t26 :caller (holder a s0) :k k0 :op :merge :kind :merge})
          state (if prepared?
                  (walk sealed [{:t :t27 :k k0 :op :merge :payload :stable :bases (:bases (m/cap sealed k0))
                                 :steps [{:id 0 :kind :merge :system :a :recovery :query}]}
                                {:t :t28 :op :merge :i 0 :outcome :unknown :committed? true}]) sealed)
          restarted (walk state [{:t :t31} {:t :t31 :phase :restart}])]
      (is (= [:recovery :durable 1] (:holder (m/cap restarted k0))))
      (is (= :merge (:kind (m/cap restarted k0))))
      (is (= :merge (:op (m/cap restarted k0))))
      (is (= (m/record state :merge) (m/record restarted :merge)))
      (when prepared?
        (refuses restarted {:t :t30 :caller (holder a s0) :k k0 :op :merge :payload :stable} ::m/stale-capability)
        (checked restarted {:t :t30 :caller [:recovery :durable 1] :k k0 :op :merge :payload :stable})
        (let [again (walk restarted [{:t :t31} {:t :t31 :phase :restart}])]
          (refuses again {:t :t30 :caller [:recovery :durable 1] :k k0 :op :merge :payload :stable} ::m/stale-capability))))))

(def spin [:spin 0])
(def run1 [spin 1])
(def run2 [spin 2])
(defn run-destination [parked?]
  (let [state (checked (scope-fixture) {:t :t04 :w b :e spin})]
    (if parked?
      (checked state {:t :t05 :w b :r run1 :kind :external :debtor [:host :native]})
      (checked state {:t :slice-enter :w b :r run1 :th :actor}))))

(deftest active-acceptance-needs-destination-activation-and-order
  (let [state (run-destination false)
        action (transfer (holder a s0) (holder b run1) k0 k1 :move)]
    (refuses state action ::m/missing-destination-order)
    (refuses state (assoc action :acceptance {:th :host :order 1}) ::m/missing-destination-order)
    (let [moved (checked state (assoc action :acceptance {:th :actor :order 1}))]
      (is (= 1 (:holder-acquisition (m/cap moved k1)))))))

(deftest incoming-parked-custody-stays-on-the-exact-generation
  (let [state (run-destination true)
        moved (checked state (transfer (holder a s0) (holder b run1) k0 k1 :move))
        reentered (checked moved {:t :t09 :w b :e spin :cause :track :order 99})]
    (is (= :exact-run (:holder-acquisition (m/cap moved k1))))
    (is (= (holder b run1) (:holder (m/cap reentered k1)))))
  (let [state (run-destination true)
        moved (checked state (transfer (holder a s0) (holder b run1) k0 k1 :move))
        retired (checked moved {:t :t11 :w b :r run1})]
    (is (= :cleanup (first (:holder (m/cap retired k1)))))
    (is (= 1 (count (get-in retired [:custody :claims]))))))

(deftest active-prefix-adopts-but-equal-suffix-and-dirty-do-not
  (doseq [[acquisition trigger adopted?] [[1 2 true] [2 2 false] [3 2 false] [0 -1 false]]]
    (let [state (run-destination false)
          moved (checked state (assoc (transfer (holder a s0) (holder b run1) k0 k1 :move)
                                      :acceptance {:th :actor :order acquisition}))
          after (checked moved {:t :t09 :w b :e spin :cause :track :order trigger})]
      (is (= (holder b (if adopted? run2 run1)) (:holder (m/cap after k1)))))))

(deftest completed-reactive-basis-accepts-exact-run-but-obsolete-basis-refuses
  (let [state (walk (scope-fixture)
                    [{:t :t02 :w b :e [:signal 0]}
                     {:t :t04 :w b :e spin}
                     {:t :t05 :w b :r run1 :kind :track :debtor [:entity b [:signal 0]]}
                     {:t :t06 :w b :o [:o 1]}
                     {:t :t07 :w b :r run1}])
        action (transfer (holder a s0) (holder b run1) k0 k1 :move)
        moved (checked state action)]
    (is (= :completed (:status (m/run state b run1))))
    (is (= :exact-run (:holder-acquisition (m/cap moved k1))))
    (let [new-generation (checked state {:t :t09 :w b :e spin :cause :track :order 0})]
      (refuses new-generation action ::m/invalid-destination))))

(deftest independent-census-detects-missing-or-forged-memberships
  (let [state (scope-fixture)]
    (is (seq (inv/custody-errors (assoc-in state [:custody :by-holder] {}))))
    (is (seq (inv/custody-errors (assoc-in state [:custody :by-holder (holder b s0)] #{k0}))))
    (is (seq (inv/custody-errors (assoc-in state (conj (m/cap-path state k0) :holder) :bare-holder))))))

(deftest repeated-explicit-cleanup-releases-live-index-and-claims
  (let [final
        (reduce (fn [state n]
                  (let [scope [:scope :id n] v [:w (inc n)] k [:cap n]
                        opened (walk state [{:t :t12 :w a :scope scope :parent [:root a]}
                                            {:t :t19 :w a :v v :k k :scope scope}
                                            {:t :t13 :w a :scope scope}
                                            {:t :queued :w v}])
                        done (finish opened k)]
                    (is (nil? (m/ent done a [:fork v])))
                    (is (empty? (:queue (m/wr done a))))
                    (is (empty? (get-in done [:custody :by-holder])))
                    (is (empty? (get-in done [:custody :claims])))
                    done)) (m/init-state) (range 128))]
    (is (= 128 (:next-claim final)))
    (is (zero? (:scope-balance (m/wr final a))))
    ;; Terminal caps/records deliberately retain affine conservation witnesses.
    (is (= 128 (count (m/all-caps final))))))

(deftest creator-publication-requires-current-activation-or-exact-run-lifetime
  (let [base (checked (independent-root (m/init-state) b) {:t :t04 :w b :e spin})
        create {:t :t19 :w b :v child :k k0 :scope run1}]
    (refuses base create ::m/missing-destination-order)
    (let [active (checked base {:t :slice-enter :w b :r run1 :th :actor})
          created (checked active (assoc create :acceptance {:th :actor :order 2}))]
      (is (= 2 (:holder-acquisition (m/cap created k0)))))
    (let [parked (checked base {:t :t05 :w b :r run1 :kind :external :debtor [:host :native]})
          created (checked parked create)
          retired (checked created {:t :t11 :w b :r run1})]
      (is (= :exact-run (:holder-acquisition (m/cap created k0))))
      (is (= :cleanup (first (:holder (m/cap retired k0))))))
    (let [newer (checked base {:t :t09 :w b :e spin :cause :dirty})]
      (refuses newer create ::m/invalid-destination))))

(deftest scope-parent-adoption-does-not-rebind-affine-custody
  (let [state (walk (m/init-state)
                    [{:t :t04 :w a :e spin}
                     {:t :t12 :w a :scope s0 :parent run1 :order 1}
                     {:t :t19 :w a :v child :k k0 :scope s0}
                     {:t :t09 :w a :e spin :cause :track :order 2}])]
    (is (= run2 (get-in state [:worlds a :scopes s0 :parent])))
    (is (= (holder a s0) (:holder (m/cap state k0))))))

(deftest root-release-claims-received-custody-without-a-fork-entity
  (let [state (checked (scope-fixture) (transfer (holder a s0) (holder b [:root b]) k0 k1 :move))
        released (checked state {:t :t34 :w b})]
    (is (= :released (:status (m/wr released b))))
    (is (= :cleanup (first (:holder (m/cap released k1)))))))

(deftest following-copies-execution-scopes-without-copying-custody
  (let [copy [:w 2]
        state (walk (m/init-state)
                    [{:t :t04 :w a :e spin}
                     {:t :t12 :w a :scope s0 :parent run1}
                     {:t :t19 :w a :v child :k k0 :scope s0}
                     {:t :t05 :w a :r run1 :kind :external :debtor [:host :native]}
                     {:t :t19 :w a :v copy :k k1 :scope [:root a]}])
        closed (checked state {:t :t13 :w copy :scope s0})]
    (is (true? (:reference? (m/ent state copy [:fork child]))))
    (is (= (holder a s0) (:holder (m/cap closed k0))))
    (is (nil? (get-in closed [:custody :by-holder (holder copy s0)])))
    (is (empty? (get-in closed [:custody :claims])))))

(deftest unpublished-cut-rollback-removes-exact-custody-membership
  (let [attached (walk (m/init-state)
                       [{:t :t20 :c [:cut 0] :scope [:root a]
                         :participants {:worlds #{a} :components #{[a :sci]} :systems #{:a}}}
                        {:t :t21 :c [:cut 0]} {:t :t22 :c [:cut 0]}
                        {:t :t23 :c [:cut 0] :v child :k k0}])
        rolled-back (checked attached {:t :t25 :c [:cut 0]})]
    (is (false? (:published? (m/cap attached k0))))
    (is (= #{k0} (get-in attached [:custody :by-holder (holder a [:root a])])))
    (is (nil? (m/cap rolled-back k0)))
    (is (empty? (get-in rolled-back [:custody :by-holder])))))

(def other-cap [:cap :other])
(def other-child [:w 2])
(defn two-cap-fixture []
  (checked (scope-fixture) {:t :t19 :w b :v other-child :k other-cap :scope s0}))
(defn consuming-actions [op]
  [{:t :t26 :k other-cap :op op :caller (holder b s0) :kind :merge}
   (transfer (holder b s0) external other-cap [:cap :successor] op)
   {:t :t33 :k other-cap :op op :caller (holder b s0)
    :successors [{:k [:cap :successor] :scope #{:a :b}}]}])

(deftest every-consumer-refuses-nil-and-reserved-operation-identities
  (let [initial (two-cap-fixture)]
    (doseq [action (consuming-actions nil)] (refuses initial action ::m/op-exists))
    (let [sealed (checked initial {:t :t26 :k k0 :op :reserved :caller (holder a s0) :kind :merge})]
      (doseq [action (consuming-actions :reserved)] (refuses sealed action ::m/op-exists)))
    (let [closed (checked initial {:t :t13 :w a :scope s0})
          event (first (:queue (m/wr closed child)))
          reserved (:op event)]
      (doseq [action (consuming-actions reserved)] (refuses closed action ::m/op-exists))
      ;; Its exact authenticated dispatch may consume the reserved operation.
      (is (= reserved (:op (m/cap (checked closed {:t :queued :w child}) k0)))))))

(deftest internal-close-allocation-skips-user-reserved-operation-names
  (let [reserved [:custody-op [:custody-claim 0]]
        initial (checked (two-cap-fixture)
                         {:t :t26 :k other-cap :op reserved :caller (holder b s0) :kind :merge})
        closed (checked initial {:t :t13 :w a :scope s0})
        event (first (:queue (m/wr closed child)))]
    (is (= [:custody-claim 1] (:custody-dispatch event)))
    (is (= 2 (:next-claim closed)))
    (checked closed {:t :t27 :k other-cap :op reserved :payload :original :steps []})
    (checked closed {:t :queued :w child})))

(deftest internal-recovery-allocation-preserves-other-sealed-and-prepared-ops
  (doseq [prepare? [false true]]
    (let [reserved [:recovery-op 1 k0 0]
          sealed (checked (two-cap-fixture)
                          {:t :t26 :k other-cap :op reserved :caller (holder b s0) :kind :merge})
          state (if prepare? (checked sealed {:t :t27 :k other-cap :op reserved :payload :original :steps []}) sealed)
          recovered (walk state [{:t :t31} {:t :t31 :phase :restart}])]
      (is (= [:recovery-op 1 k0 1] (:op (m/cap recovered k0))))
      (is (= reserved (:op (m/cap recovered other-cap))))
      (is (= :merge (:kind (m/cap recovered other-cap))))
      (is (= (m/record state reserved) (m/record recovered reserved))))))

(deftest restart-requires-an-actual-clean-process-loss
  (let [live (scope-fixture)]
    (refuses live {:t :t31 :phase :restart} ::m/not-crashed)
    (refuses (assoc live :process-live? false) {:t :t31 :phase :restart} ::m/not-crashed)
    (is (seq (inv/custody-errors (assoc live :process-live? false))))
    (let [recovered (walk live [{:t :t31} {:t :t31 :phase :restart}])]
      (refuses recovered {:t :t31 :phase :restart} ::m/not-crashed)
      (let [again (walk recovered [{:t :t31} {:t :t31 :phase :restart}])]
        (is (= [:recovery :durable 2] (:holder (m/cap again k0))))))))

(deftest independent-close-proof-rejects-coherent-revocation-and-lost-custody
  (let [before (checked (scope-fixture) (transfer (holder a s0) (holder b s0) k0 k1 :move))
        action {:t :t13 :w a :scope s0}
        after (checked before action)
        revoked (m/claim-owner-custody after b s0)]
    ;; The old fork's owner is closed; the destination is still live. All cap,
    ;; index and new claim rows agree, so only the independent edge proof catches it.
    (is (empty? (inv/custody-errors revoked)))
    (is (seq (inv/custody-edge-errors {:before before :action action :after revoked}))))
  (let [before (scope-fixture) action {:t :t13 :w a :scope s0}
        after (checked before action) id (first (keys (get-in after [:custody :claims])))
        returned (-> after
                     (m/put-cap k0 (assoc (m/cap after k0) :holder (holder b s0)))
                     (assoc-in [:custody :claims] {})
                     (assoc-in [:worlds child :queue] []))]
    (is (empty? (inv/custody-errors returned)))
    (is (seq (inv/custody-edge-errors {:before before :action action :after returned})))
    (doseq [corrupt [(assoc-in after [:custody :claims id :origin] (holder b s0))
                     (assoc-in after [:custody :claims id :anchor] [(holder b [:root b])])]]
      (is (seq (inv/custody-edge-errors {:before before :action action :after corrupt}))))))

(deftest pending-dispatch-is-an-obligation-in-both-directions
  (let [closed (checked (scope-fixture) {:t :t13 :w a :scope s0})
        event (first (:queue (m/wr closed child)))
        missing-dispatch (assoc-in closed [:worlds child :queue] [])
        missing-claim (-> closed (assoc-in [:custody :claims] {})
                          (m/put-cap k0 (assoc (m/cap closed k0) :holder (holder b s0))))]
    (is (seq (inv/custody-errors missing-dispatch)))
    (is (seq (inv/custody-errors missing-claim)))
    (refuses missing-claim {:t :queued :w child} ::m/invalid-custody-claim)
    (is (= k0 (:cap event)))))

(deftest independent-transfer-and-partition-proof-checks-authority-and-payload-metadata
  (let [before (scope-fixture)
        action (transfer (holder a s0) (holder b s0) k0 k1 :move)
        after (checked before action)]
    (doseq [cap [(assoc (m/cap after k1) :holder (holder a s0))
                 (assoc (m/cap after k1) :holder-acquisition :exact-run)
                 (assoc (m/cap after k1) :bases {:a :counterfeit})]]
      (let [corrupt (m/put-cap after k1 cap)]
        (is (seq (inv/custody-edge-errors {:before before :action action :after corrupt}))))))
  (let [before (scope-fixture)
        action {:t :t33 :k k0 :op :split :caller (holder a s0)
                :successors [{:k k1 :scope #{:a}} {:k other-cap :scope #{:b}}]}
        after (checked before action)]
    (doseq [cap [(assoc (m/cap after k1) :holder (holder b s0))
                 (assoc (m/cap after k1) :holder-acquisition :exact-run)
                 (assoc (m/cap after k1) :bases (:bases (m/cap before k0)))]]
      (is (seq (inv/custody-edge-errors {:before before :action action :after (m/put-cap after k1 cap)}))))))

(deftest independent-prefix-proof-rejects-exact-run-and-suffix-adoption
  (doseq [parked? [true false]]
    (let [state (run-destination parked?)
          moved (checked state (cond-> (transfer (holder a s0) (holder b run1) k0 k1 :move)
                                 (not parked?) (assoc :acceptance {:th :actor :order 3})))
          action {:t :t09 :w b :e spin :cause :track :order 2}
          after (checked moved action)
          corrupt (m/put-cap after k1 (assoc (m/cap after k1) :holder (holder b run2)))]
      (is (empty? (inv/custody-errors corrupt)))
      (is (seq (inv/custody-edge-errors {:before moved :action action :after corrupt}))))))

(deftest repeated-successor-transfer-and-partition-chains-conserve-live-custody
  (let [initial (independent-root (m/init-state {:external-principals #{external}}) b)
        final
        (reduce
         (fn [state n]
           (let [scope [:scope :id n] v [:w (+ 100 n)]
                 cap-id (fn [tag] [:chain-cap n tag]) op-id (fn [tag] [:chain-op n tag])
                 source (holder a scope) destination (holder b scope)
                 state (walk state
                             [{:t :t12 :w a :scope scope :parent [:root a]}
                              {:t :t12 :w b :scope scope :parent [:root b]}
                              {:t :t19 :w a :v v :k (cap-id :root) :scope scope :systems #{:a :b :c :d}}
                              {:t :t33 :k (cap-id :root) :op (op-id :split-root) :caller source
                               :successors [{:k (cap-id :ab) :scope #{:a :b}} {:k (cap-id :cd) :scope #{:c :d}}]}
                              (transfer source destination (cap-id :ab) (cap-id :ab-1) (op-id :move-1))
                              (transfer destination source (cap-id :ab-1) (cap-id :ab-2) (op-id :move-2))
                              {:t :t33 :k (cap-id :ab-2) :op (op-id :split-successor) :caller source
                               :successors [{:k (cap-id :a) :scope #{:a}} {:k (cap-id :b) :scope #{:b}}]}
                              (transfer source destination (cap-id :a) (cap-id :a-1) (op-id :move-3))
                              (transfer destination external (cap-id :a-1) (cap-id :a-2) (op-id :move-4))
                              (transfer external destination (cap-id :a-2) (cap-id :a-3) (op-id :move-5))
                              {:t :t13 :w a :scope scope} {:t :t13 :w b :scope scope}
                              {:t :queued :w v} {:t :queued :w v} {:t :queued :w v}])
                 done (reduce finish state [(cap-id :cd) (cap-id :b) (cap-id :a-3)])]
             (is (empty? (get-in done [:custody :by-holder])))
             (is (empty? (get-in done [:custody :claims])))
             (is (empty? (:queue (m/wr done a))))
             (is (empty? (:queue (m/wr done b))))
             done)) initial (range 32))]
    (is (= 96 (:next-claim final)))
    (is (= 320 (count (m/all-caps final))))
    (is (= 320 (count (m/all-records final))))))

(defn lost-custody-state [after k]
  (-> after (m/put-cap k (assoc (m/cap after k) :holder (holder a s0)))
      (assoc-in [:custody :claims] {}) (assoc-in [:worlds child :queue] [])))

(deftest independent-close-proof-includes-run-supersession-cancellation-and-root-release
  (let [parked (run-destination true)
        before (checked parked (transfer (holder a s0) (holder b run1) k0 k1 :move))
        action {:t :t11 :w b :r run1}
        after (checked before action)]
    (is (seq (inv/custody-edge-errors {:before before :action action :after (lost-custody-state after k1)}))))
  (let [completed (walk (scope-fixture)
                        [{:t :t02 :w b :e [:signal 0]} {:t :t04 :w b :e spin}
                         {:t :t05 :w b :r run1 :kind :track :debtor [:entity b [:signal 0]]}
                         {:t :t06 :w b :o [:o 1]} {:t :t07 :w b :r run1}])
        before (checked completed (transfer (holder a s0) (holder b run1) k0 k1 :move))
        action {:t :t10 :w b :r run1}
        after (checked before action)]
    (is (seq (inv/custody-edge-errors {:before before :action action :after (lost-custody-state after k1)}))))
  (let [before (checked (scope-fixture) (transfer (holder a s0) (holder b [:root b]) k0 k1 :move))
        action {:t :t34 :w b}
        after (checked before action)]
    (is (seq (inv/custody-edge-errors {:before before :action action :after (lost-custody-state after k1)})))))

(deftest independent-recovery-proof-allows-only-specified-vanished-descriptor-edits
  (let [split (walk (m/init-state)
                    [{:t :t19 :w a :v child :k k0 :scope [:root a] :systems #{:a :memory}}
                     {:t :t33 :k k0 :op :split :caller (holder a [:root a])
                      :successors [{:k k1 :scope #{:a}} {:k other-cap :scope #{:memory}}]}])
        action {:t :t31}
        crashed (checked split action)
        corrupt (assoc-in crashed [:durable :records :split :successors 0 :holder] (holder b [:root b]))]
    (is (seq (inv/custody-edge-errors {:before split :action action :after corrupt})))
    (let [restart {:t :t31 :phase :restart}
          recovered (checked crashed restart)
          altered (assoc-in recovered [:durable :records :split :successors 0 :scope] #{:forged})]
      (is (seq (inv/custody-edge-errors {:before crashed :action restart :after altered}))))))

(deftest independent-operation-and-restart-proof-detects-coherent-takeovers
  (let [before (two-cap-fixture)
        action (transfer (holder b s0) external other-cap [:cap :successor] :reserved)
        correct (checked before action)
        reserved-before (checked before {:t :t26 :k k0 :op :reserved :caller (holder a s0) :kind :merge})
        ;; Restore K's legitimate sealed row into an otherwise coherent transfer
        ;; result. Its unprepared reservation must independently fence this edge.
        stolen (m/put-cap correct k0 (m/cap reserved-before k0))]
    (is (seq (inv/custody-errors stolen)))
    (is (seq (inv/custody-edge-errors {:before reserved-before :action action :after stolen}))))
  (let [before (scope-fixture)
        takeover (-> before (assoc :restarted? true :recovery-epoch 1)
                     (m/put-cap k0 (assoc (m/cap before k0) :holder [:recovery :durable 1]
                                          :holder-acquisition nil)))]
    (is (empty? (inv/custody-errors takeover)))
    (is (seq (inv/custody-edge-errors {:before before :action {:t :t31 :phase :restart} :after takeover})))))

(deftest terminal-dispatch-duplicates-require-the-original-terminal-evidence
  (let [split (checked (scope-fixture)
                       {:t :t33 :k k0 :op :split :caller (holder a s0)
                        :successors [{:k [:cap :a] :scope #{:a}} {:k [:cap :b] :scope #{:b}}]})
        moved (checked split (transfer (holder a s0) (holder b s0) [:cap :b] k1 :move))
        closed (checked moved {:t :t13 :w a :scope s0})
        event (first (:queue (m/wr closed child)))
        done (finish (checked closed {:t :queued :w child}) [:cap :a])
        duplicate (m/enqueue done child event)
        replayed (checked duplicate {:t :queued :w child})]
    (is (not= :released (:status (m/wr done child))))
    (is (= (m/all-caps done) (m/all-caps replayed)))
    (let [forged (m/enqueue done child (assoc event :op :unrelated))]
      (is (seq (inv/custody-errors forged)))
      (refuses forged {:t :queued :w child} ::m/invalid-custody-claim))))

(deftest a-lost-process-cannot-admit-threads-or-execute-settlement
  (let [before (two-cap-fixture)
        lost (checked before {:t :t31})]
    (doseq [action (concat
                    [{:t :thread-entry :th :outside :thread {:world a :scope nil :run nil}}
                     {:t :t35 :th :outside}
                     {:t :t26 :k k0 :op :seal :caller (holder a s0) :kind :discard}
                     (transfer (holder a s0) (holder b s0) k0 k1 :move)
                     {:t :t33 :k k0 :op :split :caller (holder a s0)
                      :successors [{:k k1 :scope #{:a :b}}]}])]
      (refuses lost action ::m/process-lost))
    (is (every? #(= :t31 (:t %)) (m/enabled lost)))
    (let [restored (checked lost {:t :t31 :phase :restart})
          c (m/cap restored k0) record (m/record restored (:op c))]
      (checked restored {:t :t30 :k k0 :op (:op c) :caller [:recovery :durable 1]
                         :payload (:payload-hash record)}))
    (let [missing (dissoc lost :process-live?) invalid (assoc lost :process-live? :unknown)]
      (doseq [state [missing invalid]]
        (is (seq (inv/custody-errors state)))
        (refuses state {:t :t31 :phase :restart} ::m/invalid-process-state))))
  (let [sealed (checked (scope-fixture) {:t :t26 :k k0 :op :merge :caller (holder a s0) :kind :merge})
        prepare {:t :t27 :k k0 :op :merge :payload :stable :steps []}
        prepared (checked sealed prepare)
        pending (checked sealed (assoc prepare :steps [{:id 0 :kind :merge :system :a :recovery :retry}]))]
    (doseq [[state action] [[sealed prepare]
                            [pending {:t :t28 :op :merge :i 0 :outcome :ok}]
                            [prepared {:t :t29 :op :merge}]]]
      (let [lost (checked state {:t :t31})]
        (refuses lost action ::m/process-lost)))))

(defn compound-delivery-fixture [orders acquisition]
  (let [start (walk (scope-fixture)
                    [{:t :t02 :w b :e [:signal 0]} {:t :t04 :w b :e spin}
                     {:t :t14 :w b :e spin :pin? true}
                     {:t :slice-enter :w b :r run1 :th :actor}])
        move (fn [state]
               (checked state (assoc (transfer (holder a s0) (holder b run1) k0 k1 :move)
                                     :acceptance {:th :actor :order acquisition})))
        ;; Construct in lexical order and receive custody at its actual actor
        ;; position. Delivery order is a separate, explicit scheduler choice.
        tracked (reduce (fn [state [i order]]
                          (let [state (if (and (integer? acquisition) (<= acquisition order) (nil? (m/cap state k1)))
                                        (move state) state)]
                            (walk state [{:t :t05 :w b :r run1 :kind :track :order order
                                          :debtor [:entity b [:signal 0]]}
                                         {:t :t06 :w b :o [:o (inc i)]}]))) start (map-indexed vector (sort orders)))
        tracked (if (and (integer? acquisition) (nil? (m/cap tracked k1))) (move tracked) tracked)
        completed (walk tracked [{:t :t07 :w b :r run1} {:t :t38 :th :actor}
                                 ;; Clear the unrelated cached Spin completion so
                                 ;; a queued Signal delivery is genuinely at head.
                                 {:t :t08 :w b :e spin :debtor-world b}])
        completed (if (= :exact-run acquisition)
                    (checked completed (transfer (holder a s0) (holder b run1) k0 k1 :move)) completed)
        rank (zipmap orders (range))
        observations (get-in completed [:worlds b :obligations])
        ordered (into (sorted-map-by (fn [left right]
                                       (compare [(get rank (:order (get observations left)) -1) (pr-str left)]
                                                [(get rank (:order (get observations right)) -1) (pr-str right)]))) observations)]
    (assoc-in completed [:worlds b :obligations] ordered)))

(defn compound-delivery-action [state queued?]
  (if queued?
    [(m/enqueue state b {:completion [:signal 0] :debtor-world b :value 1 :source-change? true})
     {:t :queued :w b}]
    [state {:t :t08 :w b :e [:signal 0] :debtor-world b :value 1}]))

(deftest compound-delivery-applies-every-ordered-trigger-to-custody
  (doseq [queued? [false true]
          [orders acquisition expected]
          [[[2 3] 1 (holder b [spin 3])]
           [[2 3] 2 (holder b run1)]
           [[2 3] 3 (holder b run1)]
           [[2 3] :exact-run (holder b run1)]
           [[3 2] 1 (holder b [spin 3])]
           [[3 2] 2 (holder b [spin 2])]
           [[3 2] 3 (holder b run1)]
           [[3 2] :exact-run (holder b run1)]
           [[2 1] 1 (holder b [spin 2])]
           [[2 3 4 5] 1 (holder b [spin 5])]
           [[2 3 4 5] :exact-run (holder b run1)]]]
    (let [[before action] (compound-delivery-action (compound-delivery-fixture orders acquisition) queued?)
          after (checked before action)]
      (is (= expected (:holder (m/cap after k1))))
      (is (empty? (inv/custody-edge-errors {:before before :action action :after after})))
      (when (< (second (nth expected 3)) (inc (count orders)))
        (let [retired (checked after {:t :t07 :w b :r [spin (inc (count orders))]})
              claim (first (vals (get-in retired [:custody :claims])))]
          (is (= :cleanup (first (:holder (m/cap retired k1)))))
          (is (= expected (:origin claim))))))))

(deftest compound-delivery-claims-an-intermediate-stale-custodian-exactly-once
  (doseq [queued? [false true] [orders acquisition] [[[2 1 3] 1] [[2 1 3 4] 1]
                                                     [[4 2 5] 3] [[4 2 5 6] 3]]]
    (let [[before action] (compound-delivery-action (compound-delivery-fixture orders acquisition) queued?)
          after (checked before action)
          claims (get-in after [:custody :claims])
          claim (first (vals claims))]
      (is (= 1 (count claims)))
      (is (= (holder b [spin 2]) (:origin claim)))
      (is (= [(holder b [spin 2]) (holder b [:root b])] (:anchor claim)))
      (is (= :cleanup (first (:holder (m/cap after k1)))))
      (is (nil? (m/run after b [spin 2])))
      (is (empty? (inv/custody-edge-errors {:before before :action action :after after})))
      (let [id (first (keys claims))
            wrong-origin (-> after (assoc-in [:custody :claims id :origin] (holder b run1))
                             (assoc-in [:custody :claims id :anchor] [(holder b run1) (holder b [:root b])]))]
        (is (empty? (inv/custody-errors wrong-origin)))
        (is (seq (inv/custody-edge-errors {:before before :action action :after wrong-origin})))))))

(deftest compound-delivery-generation-and-acquisition-evidence-is-independent
  (doseq [queued? [false true]]
    (let [[before action] (compound-delivery-action (compound-delivery-fixture [2 3] 1) queued?)
          after (checked before action)
          wrong-generation (m/put-cap after k1 (assoc (m/cap after k1) :holder (holder b [spin 2])))
          wrong-before-order (m/put-cap before k1 (assoc (m/cap before k1) :holder-acquisition 2))
          wrong-after-order (m/put-cap after k1 (assoc (m/cap after k1) :holder-acquisition 2))
          wrong-clock (assoc-in after [:generation-clock [b spin]] 999)]
      (is (empty? (inv/custody-errors wrong-generation)))
      (is (seq (inv/custody-edge-errors {:before before :action action :after wrong-generation})))
      (is (seq (inv/custody-edge-errors {:before wrong-before-order :action action :after wrong-after-order})))
      (is (seq (inv/custody-edge-errors {:before before :action action :after wrong-clock}))))))

(deftest compound-delivery-supports-explicit-nondense-run-allocation-evidence
  (doseq [queued? [false true]]
    (let [[before action] (compound-delivery-action (compound-delivery-fixture [2 3] 1) queued?)
          action (assoc action :fresh-runs [[b spin 10] [b spin 20]])
          after (checked before action)]
      (is (= (holder b [spin 20]) (:holder (m/cap after k1))))
      (is (= 20 (get-in after [:generation-clock [b spin]])))
      (is (empty? (inv/custody-edge-errors {:before before :action action :after after}))))))

(deftest durable-partition-descriptors-live-with-their-actual-consuming-record
  (let [split (walk (m/init-state)
                    [{:t :t19 :w a :v child :k k0 :scope [:root a] :systems #{:a :memory}}
                     {:t :t33 :k k0 :op :split :caller (holder a [:root a])
                      :successors [{:k k1 :scope #{:a}} {:k other-cap :scope #{:memory}}]}])
        record (get-in split [:durable :records :split])
        crashed (checked split {:t :t31})
        restored (checked crashed {:t :t31 :phase :restart})]
    (is (nil? (get-in split [:records :split])))
    (is (= [k1 other-cap] (mapv :k (:successors record))))
    (doseq [state [crashed restored]]
      (is (= #{:memory} (:scope (get (m/vanished-caps state) other-cap))))
      (is (= :discarded (:disposition (get (m/vanished-caps state) other-cap)))))
    (is (seq (inv/custody-errors (assoc-in split [:records :split] {:successors (:successors record)}))))
    (is (seq (inv/custody-errors (assoc-in split [:caps k0] (m/cap split k0)))))))

(defn cross-spin-anchor-fixture [scoped? later-parent?]
  (let [parent [:spin 1] child-spin [:spin 2] p1 [parent 1] c1 [child-spin 1]
        child-scope [:scope :id 1]
        state (walk (scope-fixture)
                    (concat [{:t :t02 :w b :e [:signal 0]} {:t :t04 :w b :e parent}
                             {:t :slice-enter :w b :r p1 :th :actor}
                             {:t :t01 :w b :r p1 :e child-spin :order 0}]
                            (when scoped? [{:t :t12 :w b :scope child-scope :parent p1 :order 0}])
                            [{:t :t05 :w b :r p1 :kind :track :order 10 :debtor [:entity b [:signal 0]]}
                             {:t :t06 :w b :o [:o 1]}
                             {:t :t04 :w b :e child-spin :scope (if scoped? child-scope p1)}
                             {:t :t38 :th :actor} {:t :slice-enter :w b :r c1 :th :actor}
                             {:t :t05 :w b :r c1 :kind :track :order 2 :debtor [:entity b [:signal 0]]}
                             {:t :t06 :w b :o [:o 3]}
                             (assoc (transfer (holder a s0) (holder b c1) k0 k1 :move)
                                    :acceptance {:th :actor :order 3})
                             {:t :t05 :w b :r c1 :kind :track :order 4 :debtor [:entity b [:signal 0]]}
                             {:t :t06 :w b :o [:o 4]} {:t :t38 :th :actor}]))]
    (if later-parent?
      (walk state [{:t :slice-enter :w b :r p1 :th :actor}
                   {:t :t05 :w b :r p1 :kind :track :order 20 :debtor [:entity b [:signal 0]]}
                   {:t :t06 :w b :o [:o 5]} {:t :t38 :th :actor}]) state)))

(deftest cross-spin-adoption-freezes-the-effective-parent-at-retirement
  (doseq [queued? [false true] scoped? [false true] later-parent? [false true]]
    (let [[before action] (compound-delivery-action (cross-spin-anchor-fixture scoped? later-parent?) queued?)
          after (checked before action)
          [id claim] (first (get-in after [:custody :claims]))
          parent [:spin 1] child-spin [:spin 2]
          expected (vec (concat [(holder b [child-spin 1])]
                                (when scoped? [(holder b [:scope :id 1])])
                                [(holder b [parent 2]) (holder b [:root b])]))]
      (is (= 1 (count (get-in after [:custody :claims]))))
      (is (= expected (:anchor claim)))
      (is (= (holder b [child-spin 1]) (:origin claim)))
      (is (= (if later-parent? [parent 3] [parent 2])
             (if scoped? (get-in after [:worlds b :scopes [:scope :id 1] :parent])
                 (:owner (m/run after b [child-spin 3])))))
      (doseq [wrong-parent (cond-> [[parent 1]] later-parent? (conj [parent 3]))]
        (let [corrupt (assoc-in after [:custody :claims id :anchor]
                                (assoc expected (- (count expected) 2) (holder b wrong-parent)))]
          (is (empty? (inv/custody-errors corrupt)))
          (is (seq (inv/custody-edge-errors {:before before :action action :after corrupt}))))))))
