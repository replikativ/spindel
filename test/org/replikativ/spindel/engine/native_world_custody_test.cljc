(ns org.replikativ.spindel.engine.native-world-custody-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.lifecycle :as lifecycle]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]))

;; These are actual native operations; the audit replay supplies the independent
;; model/state/edge comparison. Cap IDs come from committed diagnostic rows.
(defn- ignore-result [_])
(defn- world-id [rt] (let [s (c/snapshot rt)] (or (:id s) (second (:root s)))))
(defn- global-state [rt] (:global (c/snapshot rt)))
(defn- live-cap [rt child]
  (first (for [[id row] (:caps (global-state rt))
               :when (and (= (world-id child) (:world row)) (= :open (:disposition row)))] [id row])))
(defn- publish [rt owner id]
  (rtp/fork-owned-world! rt {:world-id id :owner owner :systems #{} :mode :following}))
(defn- refuses-unchanged! [runtimes f]
  (let [before (mapv c/snapshot-family runtimes)]
    (is (thrown? #?(:clj Exception :cljs js/Error) (f)))
    (is (= before (mapv c/snapshot-family runtimes)))))
(defn- assert-live-empty! [rt]
  (is (= {} (get-in (global-state rt) [:custody :by-holder])))
  (is (= {} (get-in (global-state rt) [:custody :claims])))
  (let [stats (c/storage-stats rt)]
    (doseq [field [:custody-live-leaves :custody-holder-buckets :custody-claims :custody-pending]]
      (is (= 0 (get stats field)) (str field)))))

(deftest transfer-moves-disposal-to-the-new-scope
  (let [rt (c/runtime {:audit? true :cps-exit? true})
        a (lifetime/open-scope! rt :a) b (lifetime/open-scope! rt :b)
        {child :context bearer :capability} (publish rt a [:w 1])
        [old-id old-row] (live-cap rt child)
        moved (rtp/transfer-owned-world! rt bearer a rt b {:operation-id :move})
        [new-id new-row] (live-cap rt child)
        expected-holder [:execution-owner (world-id rt) :scope [:scope :id 1]]]
    (is (some? bearer))
    (is (not (identical? bearer moved)))
    (is (not= old-id new-id))
    (is (= [:execution-owner (world-id rt) :scope [:scope :id 0]] (:holder old-row)))
    (is (= expected-holder (:holder new-row)))
    (is (nil? (:holder-acquisition new-row)))
    (is (= #{new-id} (get-in (global-state rt) [:custody :by-holder expected-holder])))
    (is (= :transferred (get-in (global-state rt) [:caps old-id :disposition])))
    (refuses-unchanged! [rt]
                        #(rtp/discard-owned-world! rt bearer a {:operation-id :stale-discard}))
    (refuses-unchanged! [rt]
                        #(rtp/transfer-owned-world! rt bearer a rt b {:operation-id :stale-transfer}))
    (is (nil? (lifetime/close-scope! rt a)))
    (is (= :live (:status (c/snapshot child))))
    (is (= :open (get-in (global-state rt) [:caps new-id :disposition])))
    (is (empty? (get-in (global-state rt) [:custody :claims])))
    ;; The allocation reference belonged to old Scope A. Its removal is not
    ;; revocation of the bearer now held by B.
    (is (nil? (get-in (c/snapshot rt) [:entities [:fork (world-id child)]])))
    (is (nil? (lifetime/close-scope! rt b)))
    (is (true? (rtp/execution-owner-joined? rt b)))
    (is (= :released (:status (c/snapshot child))))
    (is (= :discarded (get-in (global-state rt) [:caps new-id :disposition])))
    (assert-live-empty! rt)
    (let [before (c/snapshot-family rt)]
      (is (nil? (lifetime/close-scope! rt b)))
      (is (= before (c/snapshot-family rt))))
    (verify-boundaries! rt)))

(deftest closure-before-transfer-refuses-in-both-orders
  (doseq [close-source? [true false]]
    (let [rt (c/runtime {:audit? true :cps-exit? true})
          a (lifetime/open-scope! rt :a) b (lifetime/open-scope! rt :b)
          {child :context bearer :capability} (publish rt a [:w 1])]
      (lifetime/close-scope! rt (if close-source? a b))
      (refuses-unchanged! [rt]
                          #(rtp/transfer-owned-world! rt bearer a rt b {:operation-id :too-late}))
      (if close-source?
        (is (= :released (:status (c/snapshot child))))
        (do (is (= :live (:status (c/snapshot child))))
            (lifetime/close-scope! rt a)))
      (assert-live-empty! rt)
      (verify-boundaries! rt))))

(deftest equal-diagnostic-coordinates-do-not-authenticate-foreign-owners-or-bearers
  (let [left (c/runtime {:audit? true :cps-exit? true})
        right (c/runtime {:audit? true :cps-exit? true})
        a (lifetime/open-scope! left :same) b (lifetime/open-scope! right :same)
        {lc :context lb :capability} (publish left a [:w 1])
        {rc :context rb :capability} (publish right b [:w 1])]
    (is (= (world-id left) (world-id right)))
    (is (= (world-id lc) (world-id rc)))
    (is (= (set (keys (:scopes (c/snapshot left))))
           (set (keys (:scopes (c/snapshot right))))))
    (doseq [attempt [#(rtp/transfer-owned-world! left lb b left a {:operation-id :wrong-caller})
                     #(rtp/transfer-owned-world! left lb a left b {:operation-id :wrong-acceptor})
                     #(rtp/transfer-owned-world! left lb a right b {:operation-id :wrong-family})
                     #(rtp/discard-owned-world! right lb b {:operation-id :wrong-bearer})
                     #(rtp/discard-owned-world! left rb a {:operation-id :other-bearer})
                     #(publish left b [:w 2])
                     #(publish left a [:w 1])]]
      (refuses-unchanged! [left right] attempt))
    (lifetime/close-scope! left a)
    (is (= :released (:status (c/snapshot lc))))
    (is (= :live (:status (c/snapshot rc))))
    (lifetime/close-scope! right b)
    (assert-live-empty! left)
    (assert-live-empty! right)
    (verify-boundaries! left)
    (verify-boundaries! right)))

(deftest root-explicit-discard-terminalizes-before-fork-reference-notification
  (let [rt (c/runtime {:audit? true :cps-exit? true}) root (lifetime/root-scope rt)
        {child :context bearer :capability} (publish rt root [:w 1])
        [id _] (live-cap rt child) values (atom []) errors (atom [])
        completion (rtp/discard-owned-world! rt bearer root {:operation-id :root-discard})]
    (is (satisfies? rtp/PCompletion completion))
    (is (not (satisfies? rtp/PWorldRelease completion)))
    (let [detach (lifecycle/observe! completion #(swap! values conj %) #(swap! errors conj %))]
      (is (ifn? detach))
      (detach) (detach))
    (is (= [nil] @values))
    (is (empty? @errors))
    (is (= :live (:status (c/snapshot rt))))
    (is (= :released (:status (c/snapshot child))))
    (is (= :discarded (get-in (global-state rt) [:caps id :disposition])))
    (is (= :discard (get-in (global-state rt) [:records :root-discard :kind])))
    (is (= [] (get-in (global-state rt) [:records :root-discard :steps])))
    (is (true? (get-in (global-state rt) [:records :root-discard :effects-released?])))
    (is (nil? (get-in (c/snapshot rt) [:entities [:fork (world-id child)]])))
    ;; Audit replay must include real T29 then T36, including the intermediate
    ;; Root fork reference. End-state absence alone cannot establish that order.
    (verify-boundaries! rt)
    (assert-live-empty! rt)
    (refuses-unchanged! [rt]
                        #(rtp/discard-owned-world! rt bearer root {:operation-id :new-discard}))))

(deftest copied-cps-finally-gates-disposal-and-detach-does-not-cancel-cleanup
  (let [rt (c/runtime {:audit? true :cps-exit? true})
        holder (lifetime/open-scope! rt :holder)
        first-gate (c/ticket :first) second-gate (c/ticket :second)
        callbacks (atom []) trace (atom []) task-errors (atom [])
        task (c/cspin rt :task
                      (let [cell (c/signal rt :cell 40)]
                        (try
                          (c/park first-gate)
                          (c/park second-gate)
                          (finally
                            (let [actual ec/*execution-context*]
                              (swap! trace conj [(world-id actual) :before (c/read-signal rt cell)]))
                            (c/await-finalization (fn [resolve _] (swap! callbacks conj resolve)))
                            (c/set-signal! rt cell 41)
                            (let [actual ec/*execution-context*]
                              (swap! trace conj [(world-id actual) :after (c/read-signal rt cell)]))))))]
    (binding [ec/*execution-context* rt]
      (c/observe! rt task ignore-result #(swap! task-errors conj %)))
    (let [{child :context bearer :capability} (publish rt holder [:w 1])
          [id _] (live-cap rt child)]
      (c/resume-ticket! child (c/pending-ticket child first-gate) :enter-child)
      (let [values (atom []) detached-values (atom []) errors (atom [])
            completion (rtp/discard-owned-world! rt bearer holder {:operation-id :physical-discard})
            detach (lifecycle/observe! completion #(swap! detached-values conj %) #(swap! errors conj %))]
        (lifecycle/observe! completion #(swap! values conj %) #(swap! errors conj %))
        (detach) (detach)
        (is (= [[(world-id child) :before 40]] @trace))
        (is (= 1 (count @callbacks)))
        (is (empty? @values))
        (is (empty? @detached-values))
        (is (true? (rtp/execution-owner-joined? rt holder))
            "Local holder join does not certify target cleanup")
        (is (false? (c/join-ready? child [:root (world-id child)])))
        (is (= :sealed (:status (c/snapshot child))))
        (is (= :sealed (get-in (global-state rt) [:caps id :disposition])))
        (is (nil? (get-in (global-state rt) [:records :physical-discard])))
        (is (seq (:cleanup-cells (c/snapshot child))))
        (let [callback (first @callbacks)]
          (callback :cleanup)
          (is (= [[(world-id child) :before 40] [(world-id child) :after 41]] @trace))
          (is (= [nil] @values))
          (is (empty? @detached-values))
          (is (empty? @errors))
          (is (= :released (:status (c/snapshot child))))
          (is (= :discarded (get-in (global-state rt) [:caps id :disposition])))
          (is (empty? (:cleanup-cells (c/snapshot child))))
          (callback :duplicate)
          (is (= [nil] @values)))
        (is (= 40 (get-in (c/snapshot rt) [:entities :cell :result])))
        (is (= :parked (get-in (c/snapshot rt) [:runs [:task 1] :status])))
        ;; The source's independent finally still owns its original cell.
        (c/cancel-spin! rt task)
        (is (= 2 (count @callbacks)))
        ((second @callbacks) :parent-cleanup)
        (is (= [[(world-id child) :before 40] [(world-id child) :after 41]
                [(world-id rt) :before 40] [(world-id rt) :after 41]] @trace))
        (assert-live-empty! rt)
        (verify-boundaries! rt)))))

(deftest root-release-composes-two-child-disposals-and-preserves-first-receipt
  (let [rt (c/runtime {:audit? true :cps-exit? true}) root (lifetime/root-scope rt)
        {a :context} (publish rt root [:w 1])
        {b :context} (publish rt root [:w 2])
        completion (rtp/request-world-release! rt :first)
        values (atom []) errors (atom [])]
    (is (identical? completion (rtp/request-world-release! rt :later)))
    (is (= :first (get-in (c/snapshot rt) [:release :reason :error])))
    (lifecycle/observe! completion #(swap! values conj %) #(swap! errors conj %))
    (is (= [nil] @values))
    (is (empty? @errors))
    (is (= :released (:status (c/snapshot rt))))
    (is (= :released (:status (c/snapshot a))))
    (is (= :released (:status (c/snapshot b))))
    (is (= 2 (count (filter #(= :discarded (:disposition %)) (vals (:caps (global-state rt)))))))
    (assert-live-empty! rt)
    (verify-boundaries! rt)))

(deftest root-release-preserves-scope-before-run-claims-and-cancellation-reason
  (doseq [run-in-scope? [false true]]
    (let [rt (c/runtime {:audit? true :cps-exit? true}) root (lifetime/root-scope rt)
          scope (lifetime/open-scope! rt :holder)
          {scope-child :context} (publish rt scope [:w 1])
          {run-child :context run-bearer :capability} (publish rt root [:w 2])
          errors (atom []) reason (ex-info "release mixed owners" {:nested? run-in-scope?})
          task (c/cspin rt :receiver
                        (rtp/transfer-owned-world! rt run-bearer root rt (lifetime/current-scope rt)
                                                   {:operation-id :to-run})
                        (c/park (c/ticket :receiver)))]
      (binding [ec/*execution-context* rt ec/*owner-scope* (if run-in-scope? scope root)]
        (c/observe! rt task ignore-result #(swap! errors conj %)))
      (let [[scope-id] (live-cap rt scope-child) [run-id] (live-cap rt run-child)]
        (rtp/request-world-release! rt reason)
        (is (= [reason] @errors))
        (is (= [:custody-op [:custody-claim 0]] (get-in (global-state rt) [:caps scope-id :op])))
        (is (= [:custody-op [:custody-claim 1]] (get-in (global-state rt) [:caps run-id :op])))
        (assert-live-empty! rt)
        (verify-boundaries! rt)))))

(deftest sibling-scope-custody-claims-have-the-models-deterministic-order
  (let [rt (c/runtime {:audit? true :cps-exit? true})
        children (mapv (fn [n]
                         (let [scope (lifetime/open-scope! rt :holder)
                               {child :context} (publish rt scope [:w (inc n)])]
                           [[:scope :id n] (first (live-cap rt child))]))
                       (range 14))]
    (rtp/request-world-release! rt :done)
    (doseq [[claim-number [_ cap]] (map-indexed vector (sort-by (comp pr-str first) children))]
      (is (= [:custody-op [:custody-claim claim-number]] (get-in (global-state rt) [:caps cap :op]))))
    (assert-live-empty! rt)
    (verify-boundaries! rt)))

(deftest release-keeps-transitive-cleanup-after-an-intermediate-claim-is-terminal
  (doseq [late-request? [false true]]
    (let [rt (c/runtime {:audit? true :cps-exit? true})
          scope (lifetime/open-scope! rt :holder)
          {middle :context} (publish rt scope [:w 1])
          inner (lifetime/open-scope! middle :inner)
          {leaf :context} (publish middle inner [:w 2])
          callback (atom nil) delivered (atom []) trace (atom [])
          task (c/cspin leaf :work
                        (let [cell (c/signal leaf :cell 40)]
                          (try
                            (c/park (c/ticket :body))
                            (finally
                              (c/await-finalization (fn [resolve _] (reset! callback resolve)))
                              (c/set-signal! leaf cell 41)
                              (swap! trace conj [(c/read-signal leaf cell) (empty? @delivered)])))))]
      (c/observe! leaf task ignore-result ignore-result)
      (when late-request? (lifetime/close-scope! rt scope))
      (let [completion (rtp/request-world-release! rt :done)]
        (lifecycle/observe! completion #(swap! delivered conj %) #(is false (str %)))
        (is (= :released (:status (c/snapshot middle))))
        (is (= :sealed (:status (c/snapshot leaf))))
        (is (empty? @delivered))
        (is (rtp/execution-owner-joined? middle (lifetime/root-scope middle)))
        (is (ifn? @callback))
        (is (= #{(world-id rt) (world-id middle)}
               (set (keys (:cleanup-targets (c/snapshot rt))))))
        (@callback :finished)
        (is (= [[41 true]] @trace))
        (is (= [nil] @delivered))
        (is (= :released (:status (c/snapshot leaf))))
        (is (empty? (:cleanup-targets (c/snapshot rt))))
        (assert-live-empty! rt)
        (verify-boundaries! rt)))))

(deftest transferred-leaves-survive-release-of-their-old-world
  (let [rt (c/runtime {:audit? true :cps-exit? true}) root (lifetime/root-scope rt)
        {keeper :context keeper-cap :capability} (publish rt root [:w 1])
        keeper-root (lifetime/root-scope keeper)
        ;; Custody of keeper itself moves away from the old world's Root;
        ;; otherwise releasing that Root would correctly dispose keeper too.
        self-cap (rtp/transfer-owned-world! rt keeper-cap root keeper keeper-root {:operation-id :move-keeper})
        new-holder (lifetime/open-scope! keeper :keeper)
        {victim :context victim-cap :capability} (publish rt root [:w 2])
        _ (rtp/transfer-owned-world! rt victim-cap root keeper new-holder {:operation-id :move-victim})
        released (atom [])]
    (lifecycle/observe! (rtp/request-world-release! rt :old-world) #(swap! released conj %) ignore-result)
    (is (= [nil] @released))
    (is (= :released (:status (c/snapshot rt))))
    (is (= :live (:status (c/snapshot keeper))))
    (is (= :live (:status (c/snapshot victim))))
    (is (= 2 (count (filter #(= :open (:disposition %)) (vals (:caps (global-state keeper)))))))
    (lifetime/close-scope! keeper new-holder)
    (is (= :released (:status (c/snapshot victim))))
    (is (= :live (:status (c/snapshot keeper))))
    (let [values (atom [])]
      (lifecycle/observe! (rtp/discard-owned-world! keeper self-cap keeper-root {:operation-id :keeper-discard})
                          #(swap! values conj %) ignore-result)
      (is (= [nil] @values)))
    (is (= :released (:status (c/snapshot keeper))))
    (assert-live-empty! keeper)
    (verify-boundaries! rt)))

(deftest active-publication-refuses-but-active-transfer-uses-the-real-cursor
  (let [rt (c/runtime {:audit? true :cps-exit? true}) root (lifetime/root-scope rt)
        {child :context bearer :capability} (publish rt root [:w 1])
        moved (atom nil) owner (atom nil)
        task (c/cspin rt :actor
                      (reset! owner (lifetime/current-scope rt))
                      (c/signal rt :prefix :value)
                      (refuses-unchanged! [rt] #(publish rt @owner [:w 2]))
                      (reset! moved (rtp/transfer-owned-world! rt bearer root rt @owner {:operation-id :active-move}))
                      (c/park (c/ticket :actor-park)))]
    (c/observe! rt task ignore-result ignore-result)
    (let [[_ row] (live-cap rt child)]
      (is (some? @moved))
      (is (= [:execution-owner (world-id rt) :run [:actor 1]] (:holder row)))
      (is (= (inc (get-in (c/snapshot rt) [:entities :prefix :order]))
             (:holder-acquisition row))))
    (c/cancel-spin! rt task)
    (is (= :released (:status (c/snapshot child))))
    (assert-live-empty! rt)
    (verify-boundaries! rt)))

(deftest ordered-reactive-reentries-adopt-only-earlier-custody
  (let [rt (c/runtime {:audit? true :cps-exit? true}) root (lifetime/root-scope rt)
        first-source (c/signal rt :first-source 0)
        second-source (c/signal rt :second-source 0)
        {a :context ca :capability} (publish rt root [:w 1])
        {b :context cb :capability} (publish rt root [:w 2])
        {d :context cd :capability} (publish rt root [:w 3])
        acquired (atom #{}) gate (c/ticket :finish)
        task (c/cspin rt :receiver
                      (when-not (contains? @acquired :a)
                        (rtp/transfer-owned-world! rt ca root rt (lifetime/current-scope rt)
                                                   {:operation-id :take-a})
                        (swap! acquired conj :a))
                      (c/track first-source)
                      (when-not (contains? @acquired :b)
                        (rtp/transfer-owned-world! rt cb root rt (lifetime/current-scope rt)
                                                   {:operation-id :take-b})
                        (swap! acquired conj :b))
                      (c/track second-source)
                      (when-not (contains? @acquired :d)
                        (rtp/transfer-owned-world! rt cd root rt (lifetime/current-scope rt)
                                                   {:operation-id :take-d})
                        (swap! acquired conj :d))
                      (c/park gate))]
    (c/observe! rt task ignore-result ignore-result)
    (c/set-signal! rt second-source 1)
    (c/resume-ticket! rt (c/pending-ticket rt gate) :second-complete)
    (is (= :released (:status (c/snapshot d))))
    (is (= [:execution-owner (world-id rt) :run [:receiver 2]]
           (:holder (second (live-cap rt a)))))
    (is (= [:execution-owner (world-id rt) :run [:receiver 2]]
           (:holder (second (live-cap rt b)))))
    (c/set-signal! rt first-source 1)
    (c/resume-ticket! rt (c/pending-ticket rt gate) :first-complete)
    (is (= :released (:status (c/snapshot b))))
    (is (= :live (:status (c/snapshot a))))
    (is (= [:execution-owner (world-id rt) :run [:receiver 3]]
           (:holder (second (live-cap rt a)))))
    (c/cancel-spin! rt task)
    (is (= :released (:status (c/snapshot a))))
    (assert-live-empty! rt)
    (verify-boundaries! rt)))

(deftest parked-and-completed-reactive-runs-accept-only-their-current-generation
  (doseq [parked? [true false]]
    (let [rt (c/runtime {:audit? true :cps-exit? true}) root (lifetime/root-scope rt)
          driver (c/signal rt :driver 0) owner (atom nil)
          task (c/cspin rt :receiver
                        (if parked?
                          (do (reset! owner (lifetime/current-scope rt))
                              (c/park (c/ticket :receiver-park)))
                          (do
                            (c/track driver)
                            ;; Reentry resumes this suffix; an earlier saved
                            ;; owner remains a literal old-generation handle.
                            (reset! owner (lifetime/current-scope rt))
                            :reactive)))
          {child :context bearer :capability} (publish rt root [:w 1])]
      (c/observe! rt task ignore-result ignore-result)
      (let [old-owner @owner
            _ (rtp/transfer-owned-world! rt bearer root rt old-owner {:operation-id :exact-move})
            [_ row] (live-cap rt child)]
        (is (= :exact-run (:holder-acquisition row)))
        (if parked?
          (c/cancel-spin! rt task)
          (do
            (c/set-signal! rt driver 1)
            (is (not (identical? old-owner @owner)))
            (let [{other :context other-cap :capability} (publish rt root [:w 2])]
              (refuses-unchanged! [rt]
                                  #(rtp/transfer-owned-world! rt other-cap root rt old-owner {:operation-id :obsolete-move}))
              (rtp/discard-owned-world! rt other-cap root {:operation-id :other-discard})
              (is (= :released (:status (c/snapshot other)))))))
        (is (= :released (:status (c/snapshot child))))
        (assert-live-empty! rt)
        (verify-boundaries! rt)))))

(deftest operation-collisions-refuse-before-consuming-the-next-leaf
  (let [rt (c/runtime {:audit? true :cps-exit? true}) root (lifetime/root-scope rt)
        scope (lifetime/open-scope! rt :holder)
        {a :context ca :capability} (publish rt root [:w 1])
        moved (rtp/transfer-owned-world! rt ca root rt scope {:operation-id :reserved})
        {b :context cb :capability} (publish rt root [:w 2])]
    (refuses-unchanged! [rt]
                        #(rtp/transfer-owned-world! rt cb root rt scope {:operation-id :reserved}))
    (refuses-unchanged! [rt]
                        #(rtp/discard-owned-world! rt cb root {:operation-id :reserved}))
    (is (= :live (:status (c/snapshot a))))
    (is (= :live (:status (c/snapshot b))))
    (rtp/discard-owned-world! rt moved scope {:operation-id :a-discard})
    (rtp/discard-owned-world! rt cb root {:operation-id :b-discard})
    (assert-live-empty! rt)
    (verify-boundaries! rt)))

(deftest unsupported-descendant-refuses-before-any-custody-teardown
  (doseq [operation [:scope :discard]]
    (let [rt (c/runtime {:audit? true :cps-exit? true})
          holder (lifetime/open-scope! rt :holder)
          {middle :context bearer :capability} (publish rt holder [:w 1])
          middle-holder (lifetime/open-scope! middle :inner)
          {leaf :context} (publish middle middle-holder [:w 2])]
      ;; The immediate target is supported; only its owned descendant has the
      ;; resource that the bounded settlement executor cannot yet dispose.
      (c/create-public-deferred! leaf nil)
      (refuses-unchanged! [rt]
                          #(case operation
                             :scope (lifetime/close-scope! rt holder)
                             :discard (rtp/discard-owned-world! rt bearer holder {:operation-id :unsupported})))
      (is (= :live (:status (c/snapshot middle))))
      (is (= :live (:status (c/snapshot leaf))))
      (is (empty? (get-in (global-state rt) [:custody :claims])))
      (is (empty? (:cleanup-targets (c/snapshot rt))))
      (verify-boundaries! rt))))

(deftest committed-cleanup-fences-new-unsupported-descendant-resources
  (let [rt (c/runtime {:audit? true :cps-exit? true})
        holder (lifetime/open-scope! rt :holder)
        {middle :context} (publish rt holder [:w 1])
        inner (lifetime/open-scope! middle :inner)
        {leaf :context} (publish middle inner [:w 2])
        callback (atom nil) timer-errors (atom [])
        task (c/cspin middle :cleanup
                      (try
                        (c/park (c/ticket :body))
                        (finally
                          (c/await-finalization (fn [resolve _] (reset! callback resolve))))))]
    (c/observe! middle task ignore-result ignore-result)
    (lifetime/close-scope! rt holder)
    (is (ifn? @callback))
    (is (= :live (:status (c/snapshot leaf))))
    (refuses-unchanged! [rt] #(c/create-public-deferred! leaf nil))
    (refuses-unchanged! [rt] #(c/create-public-mailbox! leaf nil))
    ;; Timer admission must refuse within its actual execution frame, before
    ;; adding an obligation or advancing the frame's acquisition cursor.
    (let [timer-task (c/cspin leaf :timer-attempt
                              (let [before (c/snapshot-family leaf)]
                                (try
                                  (rtp/await-public-timer! leaf 1000 nil ignore-result ignore-result)
                                  (is false "timer admission must refuse")
                                  (catch #?(:clj Throwable :cljs :default) error
                                    (swap! timer-errors conj (:error (ex-data error)))
                                    (is (= before (c/snapshot-family leaf)))))))]
      (c/observe! leaf timer-task ignore-result #(is false (str %))))
    (is (= [:unsupported-operation] @timer-errors))
    (is (empty? (:native (c/snapshot leaf))))
    (@callback :finished)
    (is (= :released (:status (c/snapshot middle))))
    (is (= :released (:status (c/snapshot leaf))))
    (assert-live-empty! rt)
    (verify-boundaries! rt)))

(deftest custody-churn-reclaims-live-indices-with-saved-data-capabilities
  (let [rt (c/runtime {:audit? true :cps-exit? true}) saved (atom [])]
    (dotimes [n 128]
      (let [a (lifetime/open-scope! rt :a) b (lifetime/open-scope! rt :b)
            {child :context bearer :capability} (publish rt a [:churn n])
            moved (rtp/transfer-owned-world! rt bearer a rt b {:operation-id [:move n]})]
        (swap! saved conj [a b bearer moved])
        (lifetime/close-scope! rt a)
        (is (= :live (:status (c/snapshot child))))
        (lifetime/close-scope! rt b)
        (is (= :released (:status (c/snapshot child))))
        (assert-live-empty! rt)
        (is (= 0 (:scope-balance (c/snapshot rt))))))
    (is (= 128 (count @saved)))
    ;; History is intentionally distinct from live custody and cannot be used
    ;; as evidence that live bucket/claim/dispatch storage was reclaimed.
    (is (= 256 (:custody-terminal-caps (c/storage-stats rt))))
    (is (= 256 (:custody-records (c/storage-stats rt))))
    (verify-boundaries! rt)))
