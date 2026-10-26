(ns org.replikativ.spindel.ygg-construction-failure-test
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.component :as component]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.quiescence :as quiescence]
            [org.replikativ.spindel.world.scope :as scope]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.yggdrasil.construction :as construction]
            [yggdrasil.protocols :as p]
            [yggdrasil.convergent :as yc]
            [yggdrasil.convergent.gset :as g]))

(defn- caught [f] (try (f) nil (catch Throwable error error)))
(defn- await-cps [op]
  (let [result (promise)]
    (op #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [[status value :as outcome] (deref result 5000 ::timeout)]
      (when (= ::timeout outcome) (throw (ex-info "CPS timed out" {})))
      (if (= :ok status) value (throw value)))))

(defn- reconcile-no-allocation! [owner]
  ;; These fixtures independently know the injected exception allocated nothing.
  (doseq [receipt (:receipts (construction/info owner))
          :when (= :uncertain (:phase receipt))]
    (construction/resolve-uncertain! owner (:id receipt) :not-acquired))
  (construction/dispose! owner {:sync? true}))

(defrecord ProbeOverlay [parent local-writes mode resources discards resource]
  p/Overlayable
  (advance! [this] this)
  (advance! [this _] this)
  (peek-parent [_] parent)
  (peek-parent [_ _] parent)
  (base-ref [_] "basis")
  (overlay-writes [_] {})
  (merge-down! [_] parent)
  (merge-down! [_ _] parent)
  (discard! [this] (p/discard! this nil))
  (discard! [_ _] (swap! discards inc) (swap! resources disj resource) parent))

(defrecord ProbeSystem [id calls resources discards captured failure fail-at]
  p/SystemIdentity
  (system-id [_] id)
  (system-type [_] :construction-probe)
  (capabilities [_] {:snapshotable true :overlayable true :branchable false})
  p/Snapshotable
  (snapshot-id [this]
    (if (:fail-snapshot? (meta this))
      (do (when-let [before (:before-snapshot (meta this))] (before)) (throw failure))
      "basis"))
  (parent-ids [_] #{})
  (as-of [_ _] nil)
  (as-of [_ _ _] nil)
  (snapshot-meta [_ _] nil)
  (snapshot-meta [_ _ _] nil)
  p/Overlayable
  (overlay [this _]
    (if (= @fail-at (swap! calls inc))
      (throw failure)
      (let [resource (random-uuid)
            result (->ProbeOverlay this (atom this) :frozen resources discards resource)]
        (swap! resources conj resource)
        (reset! captured result)
        result))))

(deftest later-constructor-failure-cleans-acknowledged-overlay-and-preserves-source
  (let [ctx (sp/create-execution-context)
        calls (atom 0) resources (atom #{}) discards (atom 0) captured (atom nil)
        failure (ex-info "Second constructor failed before allocation" {})
        fail-at (atom 2)
        a (->ProbeSystem "a" calls resources discards captured failure fail-at)
        b (->ProbeSystem "b" calls resources discards captured failure fail-at)]
    (try
      (sp/with-context ctx
        (ygg/register! a) (ygg/register! b)
        (let [error (caught #(ygg/fork! {:mode :frozen}))
              owner (:construction/owner (ex-data error))]
          (is (identical? failure (ex-cause error)))
          (is (= 2 @calls))
          (is (empty? @resources))
          (is (= 1 @discards))
          (is (construction/owner? owner))
          (is (= 1 (count (filter #(= :uncertain (:phase %)) (:receipts (construction/info owner))))))
          (reconcile-no-allocation! owner)
          (is (= :closed (:status (construction/info owner))))
          (is (identical? a @(ygg/system-signal "a")))))
      (finally (context/stop-context! ctx)))))

(deftest scope-retains-partial-construction-without-funding-or-refunding
  (let [ctx (sp/create-execution-context)
        calls (atom 0) resources (atom #{}) discards (atom 0) captured (atom nil)
        failure (ex-info "Native constructor failed" {}) fail-at (atom 2)
        authority-calls (atom [])
        authority (reify scope/PResourceAuthority
                    (grant! [_ _ _ _] (swap! authority-calls conj :grant))
                    (return! [_ _] (swap! authority-calls conj :return))
                    (balance [_ _] {}))
        world-scope (scope/create {:authority authority})]
    (try
      (sp/with-context ctx
        (doseq [id ["a" "b"]]
          (ygg/register! (->ProbeSystem id calls resources discards captured failure fail-at)))
        (let [error (caught #(await-cps (fn [resolve reject]
                                          (scope/fork! world-scope ctx resolve reject))))
              entries (vals (:recovery @world-scope))
              owner (:construction (first entries))]
          (is (= ::ygg/construction-incomplete (:type (ex-data error))))
          (is (nil? (:construction/owner (ex-data error))))
          (is (= 1 (count entries)))
          (is (empty? (scope/handles @world-scope)))
          (is (empty? (scope/descriptors world-scope)))
          (is (empty? @resources))
          (is (empty? @authority-calls))
          (reconcile-no-allocation! owner)
          (await-cps (scope/recover! world-scope))
          (is (empty? (:recovery @world-scope)))
          (is (empty? @authority-calls))
          (await-cps (scope/discard! world-scope))))
      (finally (context/stop-context! ctx)))))

(defrecord FailingCheckout [live failure]
  p/SystemIdentity
  (system-id [_] "branch")
  (system-type [_] :branch-probe)
  (capabilities [_] {:snapshotable true :branchable true})
  yc/PConvergent
  (-join [this _] this)
  (-join [this _ _] this)
  (-conflict-free? [_] true)
  p/Snapshotable
  (snapshot-id [_] "basis")
  (parent-ids [_] #{})
  (as-of [_ _] nil)
  (as-of [_ _ _] nil)
  (snapshot-meta [_ _] nil)
  (snapshot-meta [_ _ _] nil)
  p/Branchable
  (branches [_] @live)
  (branches [_ _] @live)
  (current-branch [_] :main)
  (branch! [this name] (swap! live conj name) this)
  (branch! [this name _] (p/branch! this name))
  (branch! [this name _ _] (p/branch! this name))
  (checkout [_ _] (throw failure))
  (checkout [_ _ _] (throw failure))
  (delete-branch! [this name] (swap! live disj name) this)
  (delete-branch! [this name opts]
    (if (= false (:sync? opts))
      (fn [resolve _] (swap! live disj name) (resolve this))
      (p/delete-branch! this name))))

(deftest branch-ack-is-cleaned-when-checkout-throws-without-an-adapter-owner
  (let [ctx (sp/create-execution-context) live (atom #{:main})
        failure (ex-info "Checkout failed after branch allocation" {})
        system (->FailingCheckout live failure)]
    (try
      (sp/with-context ctx
        (ygg/register! system)
        (let [error (caught #(ygg/fork!))
              owner (:construction/owner (ex-data error))
              receipts (:receipts (construction/info owner))]
          (is (identical? failure (ex-cause error)))
          (is (= 2 (count @live)) "Uncertain checkout retains its branch dependency")
          (is (= [:owned :uncertain] (mapv :phase receipts)))
          (is (= (:id (first receipts)) (:depends-on (second receipts))))
          (is (= :checkout (:kind (second receipts))))
          (reconcile-no-allocation! owner)
          (is (= #{:main} @live))
          (is (= :closed (:status (construction/info owner))))))
      (finally (context/stop-context! ctx)))))

(deftest provisional-context-work-prevents-native-release-until-physically-finished
  (let [ctx (sp/create-execution-context)
        owner (construction/create {1 "probe"}) live (atom #{:resource}) discards (atom 0)
        native (->ProbeOverlay :parent (atom nil) :frozen live discards :resource)]
    (try
      (construction/observe! owner {:phase :before :signal 1 :source :parent})
      (construction/observe! owner {:phase :value :signal 1 :source :parent :value native})
      (construction/observe! owner {:phase :context :context ctx})
      (quiescence/begin! ctx)
      (construction/failed! owner (ex-info "Later descriptor failure" {}))
      (is (= ::construction/not-quiescent (:type (ex-data (caught #(construction/dispose! owner))))))
      (is (= #{:resource} @live))
      (is (zero? @discards))
      (quiescence/end! ctx)
      (construction/dispose! owner)
      (is (empty? @live))
      (is (= 1 @discards))
      (finally (context/stop-context! ctx)))))

(deftest failed-copy-hands-off-completed-copies-and-partial-construction-together
  (let [ctx (sp/create-execution-context)
        calls (atom 0) resources (atom #{}) discards (atom 0) captured (atom nil)
        failure (ex-info "Second copy's second constructor failed" {}) fail-at (atom 6)
        claimed (atom nil) callback-calls (atom 0)]
    (try
      (sp/with-context ctx
        (doseq [id ["a" "b"]]
          (ygg/register! (->ProbeSystem id calls resources discards captured failure fail-at)))
        (let [source (ygg/fork! {:mode :frozen})
              source-resources @resources
              error (caught #(ygg/copy-fork! source 3
                                             {:on-copy-failure
                                              (fn [payload]
                                                (swap! callback-calls inc)
                                                (reset! claimed payload)
                                                true)}))
              {:keys [copies construction]} @claimed]
          (is (= 1 @callback-calls))
          (is (= 1 (count copies)))
          (is (construction/owner? construction))
          (is (:copy/claimed? (ex-data error)))
          (is (nil? (:construction/owner (ex-data error))))
          (is (ygg/open-fork? source) "Failed copy does not consume its source")
          (is (= 4 (count @resources)) "Source and one complete copy remain; partial ACK was cleaned")
          (doseq [copy copies] (ygg/discard-fork! copy))
          (reconcile-no-allocation! construction)
          (is (= source-resources @resources))
          (ygg/with-fork source (is (some? (ygg/system "a"))))
          (ygg/discard-fork! source)
          (is (empty? @resources))))
      (finally (context/stop-context! ctx)))))

(defrecord ObservedHook [id events deferred nested]
  p/SystemIdentity
  (system-id [_] id)
  (system-type [_] :observer-probe)
  (capabilities [_] {})
  rtp/PForkable
  (fork-value [this _ directive]
    (swap! events conj [:directive directive])
    (context/report-fork-event! {:phase :probe :where :before})
    (when nested (nested))
    (context/report-fork-event! {:phase :probe :where :after})
    (reset! deferred (is.simm.partial-cps.runtime/bound-fn
                       #(context/report-fork-event! {:phase :probe :where :deferred})))
    this))

(deftest native-observer-extent-is-restored-and-not-captured-in-directives-or-bound-functions
  (let [outer (sp/create-execution-context) inner (sp/create-execution-context)
        events (atom []) deferred (atom nil) outer-events (atom []) inner-events (atom [])]
    (try
      (sp/with-context inner (ygg/register! (->ObservedHook "inner" events deferred nil)))
      (let [nested (fn [] (context/fork-context inner :fork-observer #(swap! inner-events conj %)))]
        (sp/with-context outer (ygg/register! (->ObservedHook "outer" events deferred nested)))
        (context/fork-context outer :fork-observer #(swap! outer-events conj %))
        (is (= [:before :after] (mapv :where (filter #(= :probe (:phase %)) @outer-events))))
        (is (= [:before :after] (mapv :where (filter #(= :probe (:phase %)) @inner-events))))
        (is (every? #(not (contains? (second %) :fork-observer)) @events))
        (let [before [@outer-events @inner-events]]
          (@deferred)
          (context/report-fork-event! {:phase :probe :where :outside})
          (is (= before [@outer-events @inner-events]))))
      (finally (context/stop-context! outer) (context/stop-context! inner)))))

(deftest native-observer-extent-is-removed-after-a-throwing-hook
  (let [ctx (sp/create-execution-context) events (atom []) deferred (atom nil)
        observed (atom []) failure (ex-info "Hook refused" {})]
    (try
      (sp/with-context ctx
        (ygg/register! (->ObservedHook "throwing" events deferred #(throw failure))))
      (is (identical? failure (caught #(context/fork-context ctx :fork-observer (fn [event] (swap! observed conj event))))))
      (let [before @observed]
        (context/report-fork-event! {:phase :probe :where :outside})
        (is (= before @observed)))
      (finally (context/stop-context! ctx)))))

(deftest a-throwing-success-continuation-cannot-resurrect-construction-ownership
  (let [ctx (sp/create-execution-context)
        calls (atom 0) resources (atom #{}) discards (atom 0) captured (atom nil)
        failure (ex-info "Receiver failed after storing its handle" {}) fail-at (atom -1)
        received (atom nil) rejected (atom nil)]
    (try
      (sp/with-context ctx
        (ygg/register! (->ProbeSystem "a" calls resources discards captured failure fail-at))
        ((ygg/fork! {:sync? false :mode :frozen})
         (fn [handle] (reset! received handle) (throw failure))
         #(reset! rejected %))
        (is (identical? failure @rejected))
        (is (ygg/open-fork? @received))
        (is (= 1 (count @resources)))
        (is (zero? @discards))
        (ygg/discard-fork! @received)
        (is (empty? @resources)))
      (finally (context/stop-context! ctx)))))

(deftest pure-component-and-descriptor-failures-release-all-known-native-acquisitions
  (doseq [stage [:component :descriptor]]
    (let [ctx (sp/create-execution-context)
          calls (atom 0) resources (atom #{}) discards (atom 0) captured (atom nil)
          failure (ex-info "Pure world initialization failed" {:stage stage}) fail-at (atom -1)
          source (cond-> (->ProbeSystem "a" calls resources discards captured failure fail-at)
                   (= :descriptor stage) (with-meta {:fail-snapshot? true}))]
      (try
        (sp/with-context ctx
          (ygg/register! source)
          (when (= :component stage)
            (component/register! :throwing
                                 (component/forkable :source (fn [& _] (throw failure)))))
          (is (identical? failure (caught #(ygg/fork! {:mode :frozen}))))
          (is (= 1 @calls))
          (is (= 1 @discards))
          (is (empty? @resources))
          (is (identical? source @(ygg/system-signal "a"))))
        (finally (context/stop-context! ctx))))))

(deftest a-real-convergent-branch-is-released-after-later-pure-initialization-fails
  (let [ctx (sp/create-execution-context)
        system (g/gset "native" {:store-config {:backend :memory :id (random-uuid)}} {:sync? true})
        failure (ex-info "Component refused" {})]
    (try
      (sp/with-context ctx
        (ygg/register! system)
        (component/register! :throwing (component/forkable :source (fn [& _] (throw failure))))
        (is (identical? failure (caught #(ygg/fork! {:mode :frozen})))))
      (is (= #{:main} (set (p/branches system))))
      (is (= #{} (g/elements system)))
      (finally (context/stop-context! ctx)))))

(deftest a-throwing-copy-receiver-leaves-one-active-partial-owner-and-cleans-complete-copies
  (let [ctx (sp/create-execution-context)
        calls (atom 0) resources (atom #{}) discards (atom 0) captured (atom nil)
        failure (ex-info "Native failure" {}) callback-failure (ex-info "Receiver failed" {})
        fail-at (atom 6) candidate (atom nil)]
    (try
      (sp/with-context ctx
        (doseq [id ["a" "b"]]
          (ygg/register! (->ProbeSystem id calls resources discards captured failure fail-at)))
        (let [source (ygg/fork! {:mode :frozen}) original-resources @resources
              error (caught #(ygg/copy-fork! source 3
                                             {:on-copy-failure (fn [{:keys [construction]}]
                                                                 (reset! candidate construction)
                                                                 (throw callback-failure))}))
              owner (:construction/owner (ex-data error))]
          (is (identical? callback-failure (:handoff-error (ex-data error))))
          (is (= original-resources @resources))
          (is (ygg/open-fork? source))
          (is (construction/owner? owner))
          (is (= ::construction/transferred
                 (:type (ex-data (caught #(construction/dispose! @candidate))))))
          (reconcile-no-allocation! owner)
          (ygg/discard-fork! source)
          (is (empty? @resources))))
      (finally (context/stop-context! ctx)))))

(deftest suspended-provisional-child-keeps-native-resources-until-a-real-host-join
  (let [ctx (sp/create-execution-context)
        calls (atom 0) resources (atom #{}) discards (atom 0) captured (atom nil)
        failure (ex-info "Descriptor failed after child suspension" {}) fail-at (atom -1)
        suspended (promise) resumed (promise) child-state (atom nil)
        queued {:type :cont-resume :site :construction-fixture :value nil
                :resolve (fn [_]
                           (let [child ec/*execution-context* d (sp/deferred)]
                             (reset! child-state {:context child :deferred d})
                             (d (fn [_] (deliver resumed {:resources @resources}))
                                (fn [error] (deliver resumed {:error error})))
                             (quiescence/on-quiescent child #(deliver suspended true))))}
        source (with-meta (->ProbeSystem "a" calls resources discards captured failure fail-at)
                 {:fail-snapshot? true
                  :before-snapshot #(assert (= true (deref suspended 5000 ::timeout)))})]
    (try
      (sp/with-context ctx
        (ygg/register! source)
        (let [error (caught #(ygg/fork! {:mode :frozen :state-updates {:engine/pending [queued]}}))
              owner (:construction/owner (ex-data error))
              activation (first (filter #(= :activation (:kind %)) (:receipts (construction/info owner))))
              {:keys [context deferred]} @child-state]
          (is (identical? failure (ex-cause error)))
          (is (true? (quiescence/quiescent? context)) "The suspended body is quiescent, not joined")
          (is (= ::construction/activation-unjoined (:type (ex-data (:cleanup-error (ex-data error))))))
          (is (= :uncertain (:phase activation)))
          (is (= 1 (count @resources)))
          (is (zero? @discards))
          (binding [ec/*execution-context* context] (sp/deliver! deferred :continue))
          (is (= {:resources @resources} (deref resumed 5000 ::timeout)))
          (let [joined (promise)]
            (quiescence/on-quiescent context #(deliver joined true))
            (is (= true (deref joined 5000 ::timeout))))
          ;; This fixture has exactly one queued continuation and one one-shot
          ;; deferred. It completed, left no pending work, and has no producer
          ;; able to resume again: a real fixture-specific join, not a guess
          ;; from the earlier quiescence snapshot.
          (construction/resolve-uncertain! owner (:id activation) :disposed)
          (construction/dispose! owner)
          (is (empty? @resources))
          (is (= 1 @discards))))
      (finally (context/stop-context! ctx)))))

(deftest scope-copy-construction-failure-never-refunds-unfunded-complete-copies
  (let [ctx (sp/create-execution-context)
        calls (atom 0) resources (atom #{}) discards (atom 0) captured (atom nil)
        failure (ex-info "Second copy constructor failed" {}) fail-at (atom 6)
        authority-calls (atom [])
        authority (reify scope/PResourceAuthority
                    (grant! [_ _ _ _] (swap! authority-calls conj :grant))
                    (return! [_ _] (swap! authority-calls conj :return))
                    (balance [_ _] {}))
        world-scope (scope/create {:authority authority})
        activity (scope/begin-activity! world-scope :construction-fixture)]
    (try
      (sp/with-context ctx
        (doseq [id ["a" "b"]]
          (ygg/register! (->ProbeSystem id calls resources discards captured failure fail-at)))
        (let [source (await-cps #(scope/fork! world-scope ctx %1 %2))
              source-resources @resources
              error (caught #(await-cps (fn [resolve reject]
                                          (scope/copy! world-scope (:child-ctx source) 3 resolve reject))))
              partial (some :construction (vals (:recovery @world-scope)))]
          (is (= ::scope/recovery-required (:type (ex-data error))))
          (is (= [:grant] @authority-calls))
          (is (= 1 (count (scope/handles @world-scope))))
          (is (= (:fork-id (:child-ctx source)) (:fork-id (first (scope/handles @world-scope)))))
          (reconcile-no-allocation! partial)
          (await-cps (scope/recover! world-scope))
          (is (= [:grant] @authority-calls) "No grant was attempted on any failed copy")
          (is (= source-resources @resources))
          (scope/end-activity! world-scope activity)
          (await-cps (scope/discard! world-scope))
          (is (= [:grant :return] @authority-calls))
          (is (empty? @resources))))
      (finally (context/stop-context! ctx)))))
