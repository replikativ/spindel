(ns org.replikativ.spindel.engine.native-active-publication-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.lifecycle :as lifecycle]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(defn- ignore-result [_])
(defn- wid [rt] (let [s (c/snapshot rt)] (or (:id s) (second (:root s)))))
(defn- cap-row [rt child]
  (first (for [[id row] (get-in (c/snapshot rt) [:global :caps])
               :when (and (= (wid child) (:world row)) (= :open (:disposition row)))] [id row])))
(defn- finish! [rt]
  (let [values (atom []) errors (atom [])]
    (lifecycle/observe! (rtp/request-world-release! rt :finished)
                        #(swap! values conj %) #(swap! errors conj %))
    (is (= [nil] @values))
    (is (empty? @errors))
    (verify-boundaries! rt)))
(defn- refuses-unchanged! [rt f]
  (let [before (c/snapshot-family rt)]
    (is (thrown? #?(:clj Exception :cljs js/Error) (f)))
    (is (= before (c/snapshot-family rt)))))

(deftest active-native-requester-keeps-its-suffix-and-transferred-child-survives
  (doseq [transfer? [false true]]
    (let [rt (c/runtime {:audit? true :cps-exit? true}) destination (lifetime/open-scope! rt :destination)
          published (atom nil) owner (atom nil) effects (atom []) errors (atom [])
          task (c/cspin rt :requester
                        (reset! owner (lifetime/current-scope rt))
                        (try
                          (swap! effects conj [(wid ec/*execution-context*) :before])
                          (let [result (rtp/fork-owned-world! rt {:world-id [:w 1]})]
                            (reset! published result)
                            (swap! effects conj [(wid ec/*execution-context*) :after]))
                          (c/park (c/ticket :parent-suffix))
                          (finally (swap! effects conj [(wid ec/*execution-context*) :finally]))))]
      (c/observe! rt task ignore-result #(swap! errors conj %))
      (let [{child :context bearer :capability} @published
            [id row] (cap-row rt child)
            action (first (for [[action _ _] (c/audit-trace rt) :when (= :t19 (:t action))] action))]
        (is (= [[(wid rt) :before] [(wid rt) :after]] @effects))
        (is (empty? (:runs (c/snapshot child))))
        (is (not (contains? (:entities (c/snapshot child)) :requester)))
        (is (= [:execution-owner (wid rt) :run [:requester 1]] (:holder row)))
        (is (integer? (:holder-acquisition row)))
        (is (= {:th :engine :order (:holder-acquisition row)} (:acceptance action)))
        (is (true? (get-in (second (first (filter #(= :t19 (:t (first %))) (c/audit-trace rt))))
                           [:threads :engine :executing?])))
        (is (empty? (:native (c/snapshot child))))
        (when transfer?
          (rtp/transfer-owned-world! rt bearer @owner rt destination {:operation-id :move-active-child}))
        (verify-boundaries! rt)
        (c/cancel-spin! rt task)
        (is (= [[(wid rt) :before] [(wid rt) :after] [(wid rt) :finally]] @effects))
        (is (= 1 (count @errors)))
        (is (= "Cancelled" (ex-message (first @errors))))
        (if transfer?
          (do (is (= :live (:status (c/snapshot child))))
              (is (= :transferred (get-in (c/snapshot rt) [:global :caps id :disposition])))
              (lifetime/close-scope! rt destination)
              (is (= :released (:status (c/snapshot child)))))
          (is (= :released (:status (c/snapshot child)))))
        (verify-boundaries! rt)
        (finish! rt)))))

(deftest public-spin-calling-typed-publication-does-not-copy-the-requester
  (let [rt (c/runtime {:audit? true :cps-exit? true}) published (atom nil)
        at-publication (atom nil) effects (atom []) values (atom []) errors (atom [])]
    (binding [ec/*execution-context* rt]
      (let [task (spin
                  (swap! effects conj [(wid ec/*execution-context*) :before])
                  (let [result (rtp/fork-owned-world! rt {:world-id [:w 1]})]
                    (reset! published result)
                    (reset! at-publication (c/snapshot (:context result))))
                  (swap! effects conj [(wid ec/*execution-context*) :after])
                  :parent-value)
            id (spin-core/spin-id task)]
        (task #(swap! values conj %) #(swap! errors conj %))
        (is (= [:parent-value] @values))
        (is (empty? @errors))
        (is (= [[(wid rt) :before] [(wid rt) :after]] @effects))
        (is (not (contains? (:runs @at-publication) [id 1])))
        (is (not (contains? (:entities @at-publication) id)))
        (is (empty? (:native @at-publication)))
        ;; The source's completed one-shot lifetime closes its own custody.
        (is (= :released (:status (c/snapshot (:context @published)))))
        (verify-boundaries! rt)
        (finish! rt)))))

(deftest active-source-copies-only-its-parked-cohort-and-descendant-scope
  (let [rt (c/runtime {:audit? true :cps-exit? true}) gate (c/ticket :worker)
        parent-gate (c/ticket :parent) published (atom nil) copied (atom nil)
        prefixes (atom 0) suffixes (atom []) errors (atom [])
        worker (c/cspin rt :parked-worker
                        (swap! prefixes inc)
                        (let [scope (lifetime/open-scope! rt :worker-scope)]
                          (lifetime/with-owner scope
                            (let [cell (c/signal rt :worker-cell 60)]
                              (c/park gate)
                              (swap! suffixes conj [(wid ec/*execution-context*) (c/read-signal rt cell)])))))
        parent (c/cspin rt :active-parent
                        (let [result (rtp/fork-owned-world! rt {:world-id [:w 1] :owner (lifetime/root-scope rt)})]
                          (reset! published result)
                          (reset! copied (c/snapshot (:context result))))
                        (c/park parent-gate))]
    (c/observe! rt worker ignore-result #(swap! errors conj %))
    (c/observe! rt parent ignore-result #(swap! errors conj %))
    (let [child (:context @published)]
      (is (= #{[:parked-worker 1]} (set (keys (:runs @copied)))))
      (is (= :inherited (get-in @copied [:runs [:parked-worker 1] :status])))
      (is (= [:parked-worker 1] (get-in @copied [:scopes [:scope :id 0] :parent])))
      (is (= [:scope :id 0] (get-in @copied [:entities :worker-cell :owner])))
      (is (not (contains? (:entities @copied) :active-parent)))
      (is (= 1 @prefixes))
      (c/resume-ticket! child (c/pending-ticket child gate) :child-entry)
      (is (= [[(wid child) 60]] @suffixes))
      (is (= 1 @prefixes))
      (is (= :parked (get-in (c/snapshot rt) [:runs [:parked-worker 1] :status])))
      (verify-boundaries! rt)
      (finish! rt))))

(deftest active-publication-acquisition-adopts-only-before-the-trigger
  (let [rt (c/runtime {:audit? true :cps-exit? true})
        first-source (c/signal rt :first 0) second-source (c/signal rt :second 0)
        children (atom {}) gate (c/ticket :complete)
        task (c/cspin rt :receiver
                      (when-not (:a @children)
                        (swap! children assoc :a (:context (rtp/fork-owned-world! rt {:world-id [:w 1]}))))
                      (c/track first-source)
                      (when-not (:b @children)
                        (swap! children assoc :b (:context (rtp/fork-owned-world! rt {:world-id [:w 2]}))))
                      (c/track second-source)
                      (when-not (:d @children)
                        (swap! children assoc :d (:context (rtp/fork-owned-world! rt {:world-id [:w 3]}))))
                      (c/park gate))]
    (c/observe! rt task ignore-result ignore-result)
    (c/set-signal! rt second-source 1)
    (c/resume-ticket! rt (c/pending-ticket rt gate) :second-complete)
    (is (= :released (:status (c/snapshot (:d @children)))))
    (doseq [key [:a :b]]
      (is (= [:execution-owner (wid rt) :run [:receiver 2]]
             (:holder (second (cap-row rt (get @children key)))))))
    (c/set-signal! rt first-source 1)
    (c/resume-ticket! rt (c/pending-ticket rt gate) :first-complete)
    (is (= :released (:status (c/snapshot (:b @children)))))
    (is (= [:execution-owner (wid rt) :run [:receiver 3]]
           (:holder (second (cap-row rt (:a @children))))))
    (c/cancel-spin! rt task)
    (is (= :released (:status (c/snapshot (:a @children)))))
    (verify-boundaries! rt)
    (finish! rt)))

(deftest cleanup-and-unsupported-options-refuse-before-active-publication
  (let [rt (c/runtime {:audit? true :cps-exit? true}) checks (atom [])
        task (c/cspin rt :guarded
                      (refuses-unchanged! rt #(rtp/fork-owned-world! rt {:world-id [:w 1] :mode :frozen}))
                      (refuses-unchanged! rt #(rtp/fork-owned-world! rt {:world-id [:w 1] :systems #{:external}}))
                      (try (c/park (c/ticket :cancel))
                           (finally
                             (refuses-unchanged! rt #(rtp/fork-owned-world! rt {:world-id [:w 1]}))
                             (swap! checks conj :cleanup-refused))))]
    (c/observe! rt task ignore-result ignore-result)
    (is (empty? @checks))
    (c/cancel-spin! rt task)
    (is (= [:cleanup-refused] @checks))
    (is (= #{(wid rt)} (set (keys (c/snapshot-family rt)))))
    (verify-boundaries! rt)
    (finish! rt)))

(deftest running-requester-entity-can-belong-to-a-copied-parked-owner
  (let [rt (c/runtime {:audit? true :cps-exit? true}) source-world (wid rt)
        gate (c/ticket :nested-actor) actor-handle (atom nil) published (atom nil)
        at-publication (atom nil) prefixes (atom []) suffixes (atom [])
        parent-values (atom []) parent-errors (atom [])
        child-values (atom []) child-errors (atom [])
        parent (c/cspin rt :nested-parent
                        (swap! prefixes conj [(wid ec/*execution-context*) :parent])
                        (let [actor (c/cspin rt :nested-actor
                                             (swap! prefixes conj [(wid ec/*execution-context*) :actor])
                                            ;; Only the source execution publishes. A later
                                            ;; explicit child invocation is a fresh body start.
                                             (when (= source-world (wid ec/*execution-context*))
                                               (let [result (rtp/fork-owned-world! rt {:world-id [:w 1] :owner (lifetime/root-scope rt)})]
                                                 (reset! published result)
                                                 (reset! at-publication (c/snapshot (:context result)))))
                                             (let [value (c/park gate)]
                                               (swap! suffixes conj [(wid ec/*execution-context*) :actor value])
                                               value))]
                          (reset! actor-handle actor)
                          (let [value (c/await actor)]
                            (swap! suffixes conj [(wid ec/*execution-context*) :parent value])
                            value)))]
    (c/observe! rt parent #(swap! parent-values conj %) #(swap! parent-errors conj %))
    (let [child (:context @published) child-world (wid child) copied @at-publication
          parent-run (first (for [[run row] (:runs copied) :when (= :nested-parent (:spin row))] run))
          source-actor-run (first (for [[run row] (:runs (c/snapshot rt))
                                        :when (= :nested-actor (:spin row))] run))
          parent-ob (first (for [[_ ob] (:obligations copied)
                                 :when (= [:run child-world parent-run] (:creditor ob))] ob))]
      (is (some? parent-run))
      (is (= :inherited (get-in copied [:runs parent-run :status])))
      (is (= parent-run (get-in copied [:entities :nested-actor :owner])))
      (is (= parent-run (get-in copied [:entities :nested-actor :creator])))
      (is (contains? (get-in copied [:runs parent-run :creations]) :nested-actor))
      ;; The entity is selected by its parked allocation owner. Its running
      ;; generation and physical entry remain solely in the source world.
      (is (some? source-actor-run))
      (is (not-any? #(= :nested-actor (:spin %)) (vals (:runs copied))))
      (is (not (contains? (:runs copied) source-actor-run)))
      (is (empty? (:native copied)))
      (is (= [:entity source-world :nested-actor] (:debtor parent-ob)))
      (is (= :armed (:slot parent-ob)))
      (is (= [[source-world :parent] [source-world :actor]] @prefixes))
      (is (empty? @suffixes))
      (verify-boundaries! rt)
      ;; The copied local entity has no Run. Invoking the actual handle in B
      ;; starts its body there, rather than resuming A's running generation.
      (c/observe! child @actor-handle #(swap! child-values conj %) #(swap! child-errors conj %))
      (let [child-actor-run (first (for [[run row] (:runs (c/snapshot child))
                                         :when (= :nested-actor (:spin row))] run))]
        (is (some? child-actor-run))
        (is (not= source-actor-run child-actor-run))
        (is (= :parked (get-in (c/snapshot child) [:runs child-actor-run :status]))))
      (is (= [[source-world :parent] [source-world :actor] [child-world :actor]] @prefixes))
      (c/resume-ticket! child (c/pending-ticket child gate) :child-value)
      (is (= [:child-value] @child-values))
      (is (empty? @child-errors))
      (is (= [[child-world :actor :child-value]] @suffixes))
      (is (= :inherited (get-in (c/snapshot child) [:runs parent-run :status])))
      (is (empty? @parent-values))
      ;; B's parked parent still awaits A's actor, not the newly started B
      ;; actor. The source result resumes each parent's own suffix once.
      (c/resume-ticket! rt (c/pending-ticket rt gate) :source-value)
      (is (= [:source-value] @parent-values))
      (is (empty? @parent-errors))
      (is (= 1 (count (filter #{[source-world :parent :source-value]} @suffixes))))
      (is (= 1 (count (filter #{[child-world :parent :source-value]} @suffixes))))
      (is (= 1 (count (filter #{[source-world :actor :source-value]} @suffixes))))
      (is (= 4 (count @suffixes)))
      (is (= 1 (count (filter #(= :parent (second %)) @prefixes))))
      (verify-boundaries! rt)
      (finish! rt)
      (is (= [:finished] @parent-errors))
      (is (empty? @child-errors)))))
