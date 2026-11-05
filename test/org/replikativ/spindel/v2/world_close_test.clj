(ns org.replikativ.spindel.v2.world-close-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await await-finalization]]
            [org.replikativ.spindel.v2.cleanup :as cleanup]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.verify :as verify]))

(defn- env
  ([] (env false))
  ([verify?]
   (let [jobs (atom [])]
     {:world (v2/world {:verify? verify?
                        :executor (reify java.util.concurrent.Executor
                                    (execute [_ f] (swap! jobs conj f)))})
      :jobs jobs})))

(defn- pump! [{:keys [jobs]}]
  (loop [fuel 1000]
    (when-let [f (first @jobs)]
      (assert (pos? fuel) "world close failed to reach a boundary")
      (swap! jobs subvec 1)
      (.run ^Runnable f)
      (recur (dec fuel)))))

(defn- observe! [operation]
  (let [seen (atom [])]
    (v2/subscribe-world-close! operation #(swap! seen conj %))
    seen))

(defn- status [w] (v2/world-close-status w))
(defn- retired? [w] (:execution-retired? (status w)))
(defn- terminal? [w] (:terminal? (status w)))
(defn- close! [w] (v2/close-world! (v2/world-host-owner w) w))
(defn- failures [w] (:spindel/cleanup-provenance (ex-data (first (:outcome (status w))))))

(deftest empty-close-release-first-and-passive-canonical-owner
  (let [{w :world :as e} (env)
        owner (v2/world-host-owner w)
        retirement (v2/world-execution-retirement owner w)]
    (is (false? (:requested? (v2/world-close-status retirement))))
    (is (identical? owner (v2/world-host-owner w)))
    (v2/release-world! w)
    (is (identical? owner (v2/world-host-owner w)))
    (let [op (v2/close-world! owner w) seen (observe! op)]
      (pump! e)
      (is (= [[nil false]] @seen))
      (is (terminal? w))
      (is (= 0 (:runs (v2/world-close-status op))))
      (is (identical? owner (v2/world-host-owner w)))
      (is (nil? @(.-cell ^org.replikativ.spindel.v2.core.WorldHostOwner owner)))
      (is (= (:outcome (cleanup/status op)) (:outcome (cleanup/status (v2/close-world! owner w)))))
      (is (thrown? clojure.lang.ExceptionInfo (v2/register-world-settlement! owner w []))))))

(deftest held-physical-settlement-recovery-and-observer-isolation
  (let [{w :world :as e} (env) owner (v2/world-host-owner w)
        cap (v2/register-world-settlement! owner w [])
        retirement (observe! (v2/world-execution-retirement owner w))]
    (is (thrown? clojure.lang.ExceptionInfo
                 (v2/acknowledge-world-settlement! cap {:settled? true :value :too-early})))
    (let [op (close! w) withdrawn (atom [])
          withdraw (v2/subscribe-world-close! op #(swap! withdrawn conj %))
          seen (observe! op)]
      (withdraw)
      (v2/subscribe-world-close! op (fn [_] (throw (ex-info "observer" {}))))
      (pump! e)
      (is (= [[nil false]] @retirement))
      (is (not (terminal? w)))
      (v2/update-world-settlement! cap {:id :native-17 :phase :ambiguous})
      (is (= {3 {:id :native-17 :phase :ambiguous}} (:recovery (status w))))
      (is (empty? @seen))
      (is (thrown? clojure.lang.ExceptionInfo (v2/acknowledge-world-settlement! cap {:error :unknown})))
      (is (not (terminal? w)))
      (v2/acknowledge-world-settlement! cap {:settled? true :value :closed})
      (v2/acknowledge-world-settlement! cap {:settled? true :value :duplicate})
      (pump! e)
      (is (= [[nil false]] @seen))
      (is (empty? @withdrawn))
      (is (terminal? w))
      (is (= {:phase :acknowledged} @(.-cell ^org.replikativ.spindel.v2.core.WorldSettlement cap))))))

(deftest preparation-holds-retirement-through-late-owned-publication
  (let [{p :world :as e} (env) c (v2/world)
        owner (v2/world-host-owner p)
        cap (v2/register-world-settlement! owner p [:acquisition])
        reservation (:acquisition (v2/world-preparations cap))
        child-owner (v2/world-host-owner c)
        native (v2/register-world-settlement! child-owner c [])]
    (close! p)
    (is (not (retired? p)))
    (is (= 1 (:preparations (status p))))
    (v2/finish-world-preparation! reservation {:world c})
    (pump! e)
    (is (retired? c))
    (is (retired? p))
    (is (= 1 (:child-terminal (status p))))
    (is (not (terminal? p)))
    (v2/acknowledge-world-settlement! cap {:settled? true :value :parent-ready})
    (is (not (terminal? p)))
    (v2/acknowledge-world-settlement! native {:settled? true :value :native-disposed})
    (pump! e)
    (is (terminal? c))
    (is (terminal? p))
    (v2/finish-world-preparation! reservation {:disposed? true})
    (is (terminal? p))))

(deftest unsettled-preparation-rejects-ack-and-unknown-disposal
  (let [{w :world} (env) owner (v2/world-host-owner w)
        cap (v2/register-world-settlement! owner w [:a])
        reservation (:a (v2/world-preparations cap))]
    (close! w)
    (is (thrown? clojure.lang.ExceptionInfo (v2/finish-world-preparation! reservation {:disposed? :unknown})))
    (is (thrown? clojure.lang.ExceptionInfo (v2/acknowledge-world-settlement! cap {:settled? true :value :bad})))
    (is (= 1 (:preparations (status w))))
    (v2/finish-world-preparation! reservation {:disposed? true})
    (is (retired? w))
    (v2/acknowledge-world-settlement! cap {:settled? true :error (ex-info "settled error" {})})
    (is (terminal? w))
    (is (= 1 (count (failures w))))))

(deftest public-cancellation-precedes-finalizer-exit-and-world-retirement
  (doseq [verify? [false true]]
    (let [{w :world :as e} (env verify?) complete (atom nil) result (atom nil)]
      (binding [v2/*world* w]
        (let [gate (v2/deferred)
              t (task
                 (let [resource (v2/cleanup-resource (fn [cb] (reset! complete cb) nil))]
                   (try (await gate)
                        (finally (await-finalization (v2/cleanup-operation resource))))))]
          (v2/value-async t (fn [v failed?] (reset! result [v failed?])))
          (v2/cancel-task! t)
          (close! w)
          (is (v2/cancelled? (first @result)))
          (is (= 1 (:runs (status w))))
          (is (not (retired? w)))
          (@complete :physical-close)
          (pump! e)
          (is (terminal? w))
          (is (zero? (:runs (status w))))
          (when verify? (is (empty? (verify/world-close-violations w)))))))))

(defn- cycle-fixture [e]
  (let [p (:world e) child (atom nil) entered (atom false) exited (atom false)]
    (binding [v2/*world* p]
      (let [gate (v2/deferred)
            t (task
               (let [[branch c] (v2/fork)]
                 (if (= :parent branch)
                   (do (reset! child c)
                       (try (await gate)
                            (finally (reset! entered true)
                                     (await-finalization (v2/close-world! c))
                                     (reset! exited true))))
                   (await gate))))]
        (pump! e)
        {:parent p :child @child :task t :entered entered :exited exited}))))

(deftest child-settlement-never-depends-on-ancestor-retirement
  (doseq [recovery? [false true]]
    (let [e (env) {:keys [parent child entered exited]} (cycle-fixture e)
          parent-owner (v2/world-host-owner parent) child-owner (v2/world-host-owner child)
          parent-native (v2/register-world-settlement! parent-owner parent [])
          child-native (v2/register-world-settlement! child-owner child [])]
      (v2/close-world! parent-owner parent)
      (pump! e)
      (is @entered)
      (is (retired? child))
      (is (not (retired? parent)))
      (is (not @exited))
      ;; Settlement-only parent receipt is available while its lexical finalizer
      ;; waits for C terminal. This is data reconciliation, not ordinary work.
      (v2/update-world-settlement! parent-native {:id :received-child-refund :phase :accepted})
      (when recovery?
        (v2/update-world-settlement! child-native {:id :child-discard :phase :ambiguous})
        (pump! e)
        (is (not (terminal? child)))
        (is (not (retired? parent))))
      (v2/acknowledge-world-settlement! child-native {:settled? true :value :child-refunded-disposed})
      (pump! e)
      (is @exited)
      (is (terminal? child))
      (is (retired? parent))
      (is (not (terminal? parent)))
      (v2/acknowledge-world-settlement! parent-native {:settled? true :value :source-refunded-disposed})
      (pump! e)
      (is (terminal? parent)))))

(deftest direct-child-release-before-parent-request-retains-both-debts
  (let [{p :world :as e} (env) c (v2/fork! p)
        owner (v2/world-host-owner c) cap (v2/register-world-settlement! owner c [])]
    (v2/release-world! c)
    (pump! e)
    (is (= 1 (:child-terminal (status p))))
    (is (= 0 (:child-execution (status p))))
    (close! p)
    (pump! e)
    (is (retired? p))
    (is (not (terminal? p)))
    (v2/acknowledge-world-settlement! cap {:settled? true :value :closed})
    (pump! e)
    (is (terminal? p))))

(deftest fork-isolates-host-authority-and-accounting
  (let [{w :world :as e} (env true) owner (v2/world-host-owner w)
        cap (v2/register-world-settlement! owner w [])]
    (binding [v2/*world* w]
      (let [gate (v2/deferred) t (task (await gate))
            c (v2/fork! w) child-owner (v2/world-host-owner c)]
        (is (not (identical? owner child-owner)))
        (is (thrown? clojure.lang.ExceptionInfo (v2/close-world! owner c)))
        (is (= 0 (:settlements (status c))))
        (is (= 1 (:runs (status c))))
        (close! c)
        (pump! e)
        (is (terminal? c))
        (is (not (:requested? (status w))))
        (is (= 1 (:runs (status w))))
        (is (empty? (verify/world-close-violations w)))
        (is (empty? (verify/world-close-violations c)))
        (v2/cancel-task! t)
        (close! w)
        (v2/acknowledge-world-settlement! cap {:settled? true :value :closed})
        (pump! e)
        (is (terminal? w))))))

(deftest unborn-discard-drops-only-copied-execution
  (let [{w :world :as e} (env) publications (atom []) finalizers (atom 0)]
    (v2/install-handlers! w {:site #(swap! publications conj %)})
    (binding [v2/*world* w]
      (let [t (task (try (v2/savepoint :site nil) (finally (swap! finalizers inc))))
            c (v2/instantiate (first @publications))
            owner (v2/world-host-owner c)
            cap (v2/register-world-settlement! owner c [])]
        (is (aget ^objects c rw/W-UNBORN) "owner lookup must not activate the instance")
        (close! c)
        (pump! e)
        (is (retired? c))
        (is (not (terminal? c)))
        (is (zero? @finalizers))
        (v2/acknowledge-world-settlement! cap {:settled? true :value :actual-native-disposal})
        (is (terminal? c))
        (v2/abandon! (first @publications))
        (pump! e)
        (is (= 1 @finalizers))
        (v2/release! t)))))

(deftest invalid-engine-world-joins-refuse-before-request
  (let [{w :world :as e} (env) unrelated (v2/world) errors (atom [])]
    (binding [v2/*world* w]
      (let [t (task (try :ok
                         (finally
                           (try (v2/close-world! w) (catch Throwable t (swap! errors conj t)))
                           (try (v2/close-world! unrelated) (catch Throwable t (swap! errors conj t)))
                           (try (v2/world-host-owner unrelated) (catch Throwable t (swap! errors conj t))))))]
        (pump! e)
        (is (= 3 (count @errors)))
        (is (every? #(contains? #{:world-owner :world-target} (:spindel/invalid (ex-data %))) @errors))
        (is (not (:requested? (status unrelated))))
        (is (not (:requested? (status w))))
        (v2/release! t)))))

(deftest child-errors-follow-one-route-through-lexical-catch-or-abandonment
  (doseq [claim-first? [false true] catch? [false true]]
    (testing (str {:claim-first? claim-first? :catch? catch?})
      (let [e (env) p (:world e) child (atom nil) error (ex-info "child-native" {})]
        (binding [v2/*world* p]
          (let [gate (v2/deferred)
                t (task
                   (let [[branch c] (v2/fork)]
                     (if (= :parent branch)
                       (do (reset! child c)
                           (try (await gate)
                                (finally
                                  (try (await-finalization (v2/close-world! c))
                                       (catch Throwable t (when-not catch? (throw t)))))))
                       (await gate))))]
            (pump! e)
            (let [c @child owner (v2/world-host-owner c)
                  cap (v2/register-world-settlement! owner c [])]
              (if claim-first?
                (do (v2/cancel-task! t) (pump! e))
                (do (v2/close-world! owner c) (pump! e)))
              (v2/acknowledge-world-settlement! cap {:settled? true :error error})
              (pump! e)
              (when-not claim-first? (v2/cancel-task! t))
              (pump! e)
              (close! p)
              (pump! e)
              (is (terminal? p))
              (is (= (if (and claim-first? catch?) [] [error]) (mapv :error (failures p))))
              (is (empty? (v2/take-world-cleanup-report! (v2/world-host-owner p) p)))
              (is (= (count (failures p)) (count (distinct (map (juxt :origin :run :order :release :substep) (failures p)))))))))))))

(deftest automatic-child-failure-order-follows-acquisition-not-ack-order
  (let [{p :world :as e} (env) a (v2/fork! p) b (v2/fork! p)
        ca (v2/register-world-settlement! (v2/world-host-owner a) a [])
        cb (v2/register-world-settlement! (v2/world-host-owner b) b [])
        ea (ex-info "first" {}) eb (ex-info "second" {})]
    (close! p)
    (pump! e)
    (v2/acknowledge-world-settlement! cb {:settled? true :error eb})
    (pump! e)
    (v2/acknowledge-world-settlement! ca {:settled? true :error ea})
    (pump! e)
    (is (= [ea eb] (mapv :error (failures p))))
    (let [seen (observe! (close! p))]
      (is (= 1 (count @seen)))
      (is (= [ea eb] (:spindel/cleanup-failures (ex-data (ffirst @seen))))))))

(deftest report-consumption-before-child-terminal-is-never-reforwarded
  (let [{p :world :as e} (env) c (v2/fork! p) error (ex-info "consumed" {})
        owner (v2/world-host-owner c) cap (v2/register-world-settlement! owner c [])]
    (binding [v2/*world* c]
      (let [gate (v2/deferred)
            t (task (try (await gate) (finally (throw error))))]
        (close! p)
        (pump! e)
        (is (= [error] (mapv :error (v2/take-world-cleanup-report! owner c))))
        (is (empty? (v2/take-world-cleanup-report! owner c)))
        (v2/acknowledge-world-settlement! cap {:settled? true :value :closed})
        (pump! e)
        (is (terminal? p))
        (is (empty? (failures c)))
        (is (empty? (failures p)))
        (hs/fence! t)))))

(deftest transitive-join-observes-without-taking-intermediate-report-route
  (let [e (env) p (:world e) child (atom nil) grandchild (atom nil)
        error (ex-info "grandchild" {})]
    (binding [v2/*world* p]
      (let [gate (v2/deferred)
            t (task
               (let [[branch c] (v2/fork)]
                 (if (= :parent branch)
                   (do (reset! child c)
                       (try (await gate)
                            (finally (await-finalization (v2/close-world! @grandchild)))))
                   (await gate))))]
        (pump! e)
        (let [g (v2/fork! @child)
              cap (v2/register-world-settlement! (v2/world-host-owner g) g [])]
          (reset! grandchild g)
          (v2/cancel-task! t)
          (close! p)
          (pump! e)
          (is (retired? g))
          (v2/acknowledge-world-settlement! cap {:settled? true :error error})
          (pump! e)
          (is (terminal? p))
          (is (= [error] (mapv :error (failures p)))))))))

(deftest physical-resource-counter-does-not-retire-on-cancel-result
  (let [{w :world :as e} (env true) acknowledged (atom nil) result (atom nil)]
    (binding [v2/*world* w]
      (let [t (task (v2/external (fn [complete]
                                   (reset! acknowledged complete)
                                   (fn [] false))))]
        (v2/value-async t (fn [v failed?] (reset! result [v failed?])))
        (is (= 1 (:resources (status w))))
        (v2/cancel-task! t)
        (close! w)
        (is (v2/cancelled? (first @result)))
        (is (= 1 (:resources (status w))))
        (is (not (retired? w)))
        (is (empty? (verify/world-close-violations w)))
        (@acknowledged :actual-exit)
        (pump! e)
        (is (terminal? w))
        (is (empty? (verify/world-close-violations w)))))))

(deftest unrelated-equal-numeric-world-ids-do-not-confer-host-authority
  (let [a (v2/world) b (v2/world) owner (v2/world-host-owner a)
        before (status b)]
    (is (= (aget ^objects a rw/ID) (aget ^objects b rw/ID)))
    (is (thrown? clojure.lang.ExceptionInfo (v2/close-world! owner b)))
    (is (thrown? clojure.lang.ExceptionInfo (v2/world-execution-retirement owner b)))
    (is (thrown? clojure.lang.ExceptionInfo (v2/register-world-settlement! owner b [:bad])))
    (is (= before (status b)))))

(deftest concurrent-close-and-owner-observation-share-one-milestone
  (let [w (v2/world) owner (v2/world-host-owner w)
        cap (v2/register-world-settlement! owner w [])
        calls (mapv (fn [_] (future [(v2/world-host-owner w) (v2/close-world! owner w)])) (range 12))
        results (mapv #(deref % 5000 ::timeout) calls)]
    (is (not-any? #{::timeout} results))
    (is (every? #(identical? owner (first %)) results))
    (let [seen (mapv #(observe! (second %)) results)]
      (is (every? #(empty? @%) seen))
      (v2/acknowledge-world-settlement! cap {:settled? true :value :closed})
      (is (every? #(= [[nil false]] @%) seen))
      (is (every? #(identical? owner (first %)) results)))))

(deftest queued-ordinary-creation-after-a-prior-release-item-cannot-resurrect
  (let [{w :world :as e} (env) refused (atom nil)]
    ;; Both ordinary calls were submitted before the request was processed.
    ;; FIFO puts the release transition first; admission must be checked again
    ;; at authoritative creation, before any run/resource/row mutation.
    (hs/mpsc-add! (aget ^objects w rw/W-INGRESS) #(v2/release-world! w))
    (v2/host! w #(v2/signal w :late) #(reset! refused %) nil)
    (pump! e)
    (is (:spindel/released (ex-data @refused)))
    (is (terminal? w))
    (is (= [0 0] ((juxt :runs :resources) (status w))))))

(deftest preparation-cannot-publish-an-ancestor-or-self-and-keeps-its-debt
  (let [{p :world :as e} (env) c (v2/fork! p)
        cap (v2/register-world-settlement! (v2/world-host-owner c) c [:a])
        reservation (:a (v2/world-preparations cap))]
    (doseq [invalid [c p]]
      (let [before (status c)]
        (is (thrown? clojure.lang.ExceptionInfo (v2/finish-world-preparation! reservation {:world invalid})))
        (is (= before (status c)))))
    (close! c)
    (v2/finish-world-preparation! reservation {:disposed? true})
    (v2/acknowledge-world-settlement! cap {:settled? true :value :closed})
    (pump! e)
    (is (terminal? c))))

(deftest recovery-projection-rejects-live-controls-without-mutation
  (let [w (v2/world) cap (v2/register-world-settlement! (v2/world-host-owner w) w [])]
    (close! w)
    (let [before (status w)]
      (is (thrown? clojure.lang.ExceptionInfo
                   (v2/update-world-settlement! cap {:id :bad :controller (fn [] w)})))
      (is (= before (status w))))
    (v2/acknowledge-world-settlement! cap {:settled? true :value :closed})
    (is (terminal? w))))

(deftest activation-needs-parent-admission-and-has-one-winning-value
  (doseq [mode [:accept :parent-closed :child-closed]]
    (testing (name mode)
      (let [{p :world :as e} (env) pubs (atom []) suffix (atom [])
            queued (atom []) original-host v2/host! original-internal @#'v2/internal!]
        (v2/install-handlers! p {:s #(swap! pubs conj %)})
        (binding [v2/*world* p]
          (let [t (task (let [v (v2/savepoint :s nil)] (swap! suffix conj v) v))
                c (v2/instantiate (first @pubs)) owner (v2/world-host-owner c)
                native (v2/register-world-settlement! owner c [])
                intercept (fn [original]
                            (fn [w f]
                              (if (identical? w p) (do (swap! queued conj f) nil) (original w f))))]
            (with-redefs-fn
              {#'v2/host! (intercept original-host) #'v2/internal! (intercept original-internal)}
              (fn []
                (is (identical? c (v2/activate! c :first)))
                (v2/activate! c :duplicate)
                (is (aget ^objects c rw/W-UNBORN) "queued parent admission cannot execute the instance")
                (is (empty? @suffix))
                (is (= 1 (count @queued)) "one child-gate claim owns the first activation value")
                (case mode
                  :parent-closed (original-internal p #(#'v2/release-world* p))
                  :child-closed (original-internal c #(#'v2/release-world* c))
                  :accept nil)))
            (doseq [admit @queued] (original-internal p admit))
            (pump! e)
            (if (= :accept mode)
              (do (is (= [:first] @suffix))
                  (is (not (aget ^objects c rw/W-UNBORN))))
              (do (is (empty? @suffix))
                  (is (aget ^objects c rw/W-UNBORN))
                  (is (retired? c))
                  (is (not (terminal? c)))
                  (is (nil? (aget ^objects c rw/W-HOLDER)))))
            (close! p)
            (pump! e)
            (if (= :accept mode)
              (is (not (terminal? p)) "accepted publication owns child's physical settlement")
              (is (terminal? p) "a refused unborn publication creates no late parent debt"))
            (v2/acknowledge-world-settlement! native {:settled? true :value :native-disposed})
            (pump! e)
            (is (terminal? c))
            (is (terminal? p))
            (hs/fence! t)))))))

(deftest parent-request-after-admission-prevents-delayed-child-birth
  (let [{p :world :as e} (env) pubs (atom []) suffix (atom []) queued (atom [])
        original-internal @#'v2/internal!]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (let [t (task (swap! suffix conj (v2/savepoint :s nil)))
            c (v2/instantiate (first @pubs))]
        ;; Permit the initial child claim, hold the parent admission, then hold
        ;; child delivery after accepting its holder. Every boundary is manual.
        (with-redefs-fn
          {#'v2/internal! (fn [w f]
                            (if (identical? w p) (do (swap! queued conj f) nil)
                                (original-internal w f)))}
          #(v2/activate! c :must-not-run))
        (let [admit (first @queued)]
          (reset! queued [])
          (with-redefs-fn
            {#'v2/internal! (fn [w f]
                              (if (identical? w c) (do (swap! queued conj f) nil)
                                  (original-internal w f)))}
            (fn []
              (original-internal p admit)
              (is (some? (aget ^objects c rw/W-HOLDER)))
              (is (aget ^objects c rw/W-UNBORN))
              (original-internal p #(#'v2/release-world* p))
              (is (not (:execution-retired? (aget ^objects p rw/W-CLOSE))))))
          (doseq [delivery @queued] (original-internal c delivery)))
        (pump! e)
        (is (empty? @suffix))
        (is (terminal? c))
        (is (terminal? p))
        (hs/fence! t)))))

(deftest activation-barrier-orders-ordinary-work-and-withdraws-before-admission
  (doseq [accept? [false true]]
    (let [{p :world :as e} (env true) pubs (atom []) suffix (atom []) queued (atom [])
          original-internal @#'v2/internal! observed (atom []) read (atom []) canceled (atom [])
          bodies (atom 0) host-effects (atom [])]
      (v2/install-handlers! p {:s #(swap! pubs conj %)})
      (binding [v2/*world* p]
        (let [x (v2/signal :before)
              t (task (v2/savepoint :s nil))
              c (v2/instantiate (first @pubs)) local-x (v2/in-world c x) local-t (v2/in-world c t)]
          (is (thrown? clojure.lang.ExceptionInfo (v2/observe! local-x (fn [_ _] nil))))
          (with-redefs-fn
            {#'v2/internal! (fn [w f]
                              (if (identical? w p) (do (swap! queued conj f) nil)
                                  (original-internal w f)))}
            (fn []
              (v2/activate! c :result)
              (v2/write! local-x :after)
              (v2/pin! local-x)
              (v2/unpin! local-x)
              (v2/observe! local-x (fn [v failed?] (swap! observed conj [v failed?])))
              (let [withdraw (v2/value-async local-t (fn [v failed?] (swap! canceled conj [v failed?])))]
                (withdraw))
              (is (= ::timeout (v2/value local-t 0 ::timeout)))
              (v2/value-async local-t (fn [v failed?] (swap! read conj [v failed?])))
              (binding [v2/*world* c] (task (swap! bodies inc)))
              (v2/host! c #(swap! host-effects conj :ordinary))
              (is (zero? @bodies))
              (is (empty? @read))
              (is (empty? @observed))
              (is (empty? @host-effects))
              (when-not accept? (original-internal p #(#'v2/release-world* p)))))
          (doseq [admit @queued] (original-internal p admit))
          (pump! e)
          (is (empty? @canceled) "withdrawal/timeout wins before any stale replay")
          (is (= 1 (count @read)))
          (is (= 1 (count @observed)))
          (if accept?
            (do (is (= [[:result false]] @read))
                (is (= [[:after false]] @observed))
                (is (= 1 @bodies))
                (is (= [:ordinary] @host-effects)))
            (do (is (:spindel/released (ex-data (ffirst @read))))
                (is (:spindel/released (ex-data (ffirst @observed))))
                (is (zero? @bodies))
                (is (empty? @host-effects))))
          (close! p)
          (pump! e)
          (is (terminal? p))
          (is (terminal? c))
          (is (zero? (:deferred-host (status c))))
          (is (empty? (verify/world-close-violations c)))
          (hs/fence! t))))))

(deftest post-activation-observation-enrolls-before-the-first-child-turn
  (let [{p :world :as e} (env) pubs (atom []) seen (atom []) result (atom []) withdrawn (atom [])]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (let [x (v2/signal :before) t (task (v2/savepoint :s nil))
            c (v2/instantiate (first @pubs)) local-x (v2/in-world c x) local-t (v2/in-world c t)]
        (aset ^objects c rw/W-INLINE false)
        (v2/activate! c :value)
        (is (nil? (aget ^objects c rw/W-ACTIVATION)) "the child claim has not executed")
        (is (hs/flag? (aget ^objects c rw/W-ACTIVATION-INTENT)))
        (v2/observe! local-x (fn [v failed?] (swap! seen conj [v failed?])))
        (let [withdraw (v2/observe! local-x (fn [v failed?] (swap! withdrawn conj [v failed?])))]
          (withdraw))
        (v2/value-async local-t (fn [v failed?] (swap! result conj [v failed?])))
        (is (empty? @seen))
        (pump! e)
        (is (= [[:before false]] @seen))
        (is (= [[:value false]] @result))
        (is (empty? @withdrawn))
        (close! p)
        (pump! e)
        (is (:terminal? (aget ^objects p rw/W-CLOSE)))
        (is (:terminal? (aget ^objects c rw/W-CLOSE)))
        (hs/fence! t)))))

(deftest activation-refusal-completes-a-deferred-host-call-promise
  (doseq [accept? [false true]]
    (let [{p :world :as e} (env) pubs (atom []) pending (atom []) effect (atom 0)
          arrived (promise) caller (atom nil)
          original-internal @#'v2/internal! original-host v2/host!]
      (v2/install-handlers! p {:s #(swap! pubs conj %)})
      (binding [v2/*world* p]
        (let [t (task (v2/savepoint :s nil)) c (v2/instantiate (first @pubs))]
          (with-redefs-fn
            {#'v2/internal! (fn [w f]
                              (if (identical? w p) (do (swap! pending conj f) nil)
                                  (original-internal w f)))
             #'v2/host! (fn [& args]
                          (let [result (apply original-host args)]
                            (when (identical? c (first args)) (deliver arrived true))
                            result))}
            (fn []
              (v2/activate! c :value)
              (reset! caller (future (try [:value (v2/host-call! c #(swap! effect inc))]
                                          (catch Throwable t [:error t]))))
              (is (= true (deref arrived 5000 ::timeout)) "host-call is actually queued behind the claim")
              (is (zero? @effect))
              (when-not accept? (original-internal p #(#'v2/release-world* p)))))
          (doseq [admit @pending] (original-internal p admit))
          (pump! e)
          (let [[kind value] (deref @caller 5000 [::timeout nil])]
            (if accept?
              (do (is (= [:value 1] [kind value])) (is (= 1 @effect)))
              (do (is (= :error kind))
                  (is (:spindel/released (ex-data value)))
                  (is (zero? @effect)))))
          (close! p)
          (pump! e)
          (is (terminal? p))
          (hs/fence! t))))))

(deftest activation-intent-before-claim-submission-never-grants-demand
  (doseq [mode [:accept :parent-closed :child-closed]]
    (let [{p :world :as e} (env true) pubs (atom []) read (atom []) observed (atom [])
          submit (atom []) bodies (atom 0)]
      (v2/install-handlers! p {:s #(swap! pubs conj %)})
      (binding [v2/*world* p]
        (let [x (v2/signal :value) t (task (v2/savepoint :s nil))
              c (v2/instantiate (first @pubs)) local-x (v2/in-world c x) local-t (v2/in-world c t)]
          ;; Pause the submitter after its atomic intent but BEFORE it queues
          ;; any child claim. Other host threads can enter this exact window.
          (with-redefs-fn {#'v2/after-gate-action! (fn [f] (swap! submit conj f))}
            #(v2/activate! c :result))
          (is (= 1 (count @submit)))
          (is (nil? (aget ^objects c rw/W-ACTIVATION)))
          (v2/observe! local-x (fn [v failed?] (swap! observed conj [v failed?])))
          (v2/value-async local-t (fn [v failed?] (swap! read conj [v failed?])))
          (v2/host! c #(swap! bodies inc))
          (pump! e)
          (is (nil? (:identity (aget ^objects c rw/W-ACTIVATION))))
          (is (= 3 (:deferred-host (status c))))
          (is (:activation-pending? (status c)))
          (is (zero? (hs/msize (aget ^objects c rw/W-ROOTS))) "no observer/wait edge or demand before admission")
          (is (empty? @read))
          (is (empty? @observed))
          (is (zero? @bodies))
          (case mode
            :parent-closed (close! p)
            :child-closed (v2/release-world! c)
            :accept nil)
          (doseq [enqueue @submit] (enqueue))
          (pump! e)
          (if (= :accept mode)
            (do (is (= [[:result false]] @read))
                (is (= [[:value false]] @observed))
                (is (= 1 @bodies)))
            (do (is (= 1 (count @read)))
                (is (= 1 (count @observed)))
                (is (:spindel/released (ex-data (ffirst @read))))
                (is (:spindel/released (ex-data (ffirst @observed))))
                (is (zero? @bodies))))
          (close! p)
          (pump! e)
          (is (terminal? p))
          (is (terminal? c))
          (is (not (:activation-pending? (status c))))
          (is (zero? (:deferred-host (status c))))
          (hs/fence! t))))))

(defn- pending-instance [e]
  (let [p (:world e) pubs (atom []) admission (atom []) original-internal @#'v2/internal!]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (let [t (task (v2/savepoint :s nil)) c (v2/instantiate (first @pubs))]
        (with-redefs-fn
          {#'v2/internal! (fn [w f]
                            (if (identical? w p) (do (swap! admission conj f) nil)
                                (original-internal w f)))}
          #(v2/activate! c :result))
        {:parent p :child c :task t :admit (fn [] (doseq [f @admission] (original-internal p f)))}))))

(deftest replay-failure-preserves-later-read-and-host-call-promise
  (let [e (env) {:keys [parent child task admit]} (pending-instance e)
        read (atom []) order (atom []) arrived (promise) caller (atom nil)
        original-host v2/host!]
    (try
      (v2/host! child #(throw (ex-info "first queued body" {})))
      (v2/host! child #(swap! order conj :middle))
      (v2/host! child #(throw (ex-info "middle queued body" {})))
      (with-redefs-fn
        {#'v2/host! (fn [& args]
                      (let [result (apply original-host args)]
                        (when (identical? child (first args)) (deliver arrived true)) result))}
        (fn []
          (reset! caller (future (try [:ok (v2/host-call! child #(do (swap! order conj :promise) :value))]
                                      (catch Throwable error [:error error]))))
          (is (= true (deref arrived 5000 ::timeout)))))
      (v2/value-async (v2/in-world child task) (fn [v failed?] (swap! read conj [v failed?])))
      (admit)
      (pump! e)
      (is (= [:middle :promise] @order))
      (is (= [:ok :value] (deref @caller 1000 ::timeout)))
      (is (= [[:result false]] @read))
      (close! parent)
      (pump! e)
      (is (terminal? parent))
      (finally (when @caller (future-cancel @caller))))))

(deftest replay-obeys-budget-and-allows-release-and-physical-ack-to-interleave
  (let [e (env) {:keys [parent child admit]} (pending-instance e) bodies (atom [])
        cap (v2/register-world-settlement! (v2/world-host-owner child) child [])]
    (aset ^objects child rw/W-BUDGET 2)
    (dotimes [i 12] (v2/host! child #(swap! bodies conj i)))
    (admit)
    (is (<= (count @bodies) 2) "activation does not replay the backlog in its one ingress unit")
    (let [before (count @bodies)]
      (#'v2/internal! child #(#'v2/release-world* child))
      (is (= before (count @bodies)) "internal release revokes the remaining ordinary bodies")
      (v2/acknowledge-world-settlement! cap {:settled? true :value :physical-exit})
      (pump! e)
      (is (= before (count @bodies)))
      (is (terminal? child)))
    (close! parent)
    (pump! e)
    (is (terminal? parent))))

(defn- queued-controls [w operations]
  (let [entered (promise) unlock (java.util.concurrent.CountDownLatch. 1)
        submitted (vec (repeatedly (count operations) promise)) count-submitted (atom -1)
        callers (atom []) original-internal @#'v2/internal!
        holder (future (#'v2/internal-call! w (fn [] (deliver entered true) (.await unlock))))]
    (try
      (is (= true (deref entered 5000 ::timeout)))
      (with-redefs-fn
        {#'v2/internal! (fn [target f]
                          (let [result (original-internal target f)]
                            (when (identical? w target)
                              (let [i (swap! count-submitted inc)]
                                (when (< i (count submitted)) (deliver (nth submitted i) true))))
                            result))}
        (fn []
          (doseq [[i operation] (map-indexed vector operations)]
            (swap! callers conj (future (try [:ok (operation)] (catch Throwable error [:error error]))))
            (is (= true (deref (nth submitted i) 5000 ::timeout))
                "each contender captured pending authority before the target gate opens"))
          (.countDown unlock)))
      (mapv #(deref % 5000 ::timeout) @callers)
      (finally (.countDown unlock)
               (future-cancel holder)
               (doseq [caller @callers] (future-cancel caller))))))

(deftest queued-duplicate-acknowledgements-recheck-terminal-phase-under-gate
  (let [w (v2/world) cap (v2/register-world-settlement! (v2/world-host-owner w) w [])
        error (ex-info "one physical error" {})]
    (close! w)
    (is (= [[:ok nil] [:ok nil]]
           (queued-controls w [#(v2/acknowledge-world-settlement! cap {:settled? true :error error})
                               #(v2/acknowledge-world-settlement! cap {:settled? true :error error})])))
    (is (terminal? w))
    (is (= [error] (mapv :error (failures w))))))

(deftest queued-preparation-completions-and-update-after-ack-are-inert
  (let [w (v2/world) cap (v2/register-world-settlement! (v2/world-host-owner w) w [:a])
        reservation (:a (v2/world-preparations cap))]
    (close! w)
    (is (= [[:ok nil] [:ok nil]]
           (queued-controls w [#(v2/finish-world-preparation! reservation {:disposed? true})
                               #(v2/finish-world-preparation! reservation {:disposed? true})])))
    (is (retired? w))
    (is (= [[:ok nil] [:ok nil]]
           (queued-controls w [#(v2/acknowledge-world-settlement! cap {:settled? true :value :closed})
                               #(v2/update-world-settlement! cap {:id :late-notification :phase :pending})])))
    (is (terminal? w))
    (is (empty? (:recovery (status w))))))

(deftest queued-before-intent-reads-and-writes-retain-preactivation-semantics
  (let [{p :world :as e} (env) pubs (atom []) before (atom []) after (atom [])]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (let [x (v2/signal :initial) t (task (v2/savepoint :s nil))
            c (v2/instantiate (first @pubs)) local-x (v2/in-world c x) local-t (v2/in-world c t)]
        (aset ^objects c rw/W-INLINE false)
        (v2/write! local-x :preactivate)
        (v2/value-async local-t (fn [v failed?] (swap! before conj [v failed?])))
        (v2/activate! c :result)
        (v2/value-async local-t (fn [v failed?] (swap! after conj [v failed?])))
        (pump! e)
        (is (= 1 (count @before)))
        (is (:spindel/unborn (ex-data (ffirst @before))))
        (is (= [[:result false]] @after))
        (aset ^objects c rw/W-INLINE true)
        (is (= :preactivate (v2/value local-x)))
        (close! p)
        (pump! e)
        (is (terminal? p))))))

(deftest child-release-between-parent-guard-and-holder-publication-is-joined
  (let [{p :world :as e} (env) pubs (atom []) ran (atom false)
        original-own @#'v2/own-child!]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (let [t (task (v2/savepoint :s nil) (reset! ran true))
            c (v2/instantiate (first @pubs))
            cap (v2/register-world-settlement! (v2/world-host-owner c) c [])
            error (ex-info "late-owned native error" {})]
        (with-redefs-fn
          {#'v2/own-child! (fn [parent scope child strong?]
                             (when (and (identical? parent p) (identical? child c))
                               ;; Parent admission already passed its guard. A
                               ;; separate thread can now release the holderless
                               ;; child without ever taking the parent's gate.
                               (let [released (future (#'v2/internal-call! c #(#'v2/release-world* c)))]
                                 (try (is (not= ::timeout (deref released 5000 ::timeout)))
                                      (finally (future-cancel released)))))
                             (original-own parent scope child strong?))}
          #(v2/activate! c :must-not-run))
        (pump! e)
        (is (false? @ran))
        (is (retired? c))
        (is (= 0 (:child-execution (status p))))
        (is (= 1 (:child-terminal (status p))) "stale delivery must reconcile the newly installed owner holder")
        (v2/acknowledge-world-settlement! cap {:settled? true :error error})
        (pump! e)
        (let [owner (v2/world-host-owner p)]
          (is (= [error] (mapv :error (v2/take-world-cleanup-report! owner p))))
          (is (empty? (v2/take-world-cleanup-report! owner p))))
        (close! p)
        (pump! e)
        (is (terminal? p))
        (is (empty? (failures p)))
        (hs/fence! t)))))

(defn- claimed-holder-retention-fixture []
  (let [{p :world :as e} (env) c (v2/fork! p)
        cap (v2/register-world-settlement! (v2/world-host-owner c) c [])
        holder (aget ^objects c rw/W-HOLDER) target-flag (aget ^objects holder 2)
        original-flag? hs/flag? intercepted (atom false)]
    (with-redefs-fn
      {#'hs/flag? (fn [flag]
                    (let [result (original-flag? flag)]
                      (when (and (identical? target-flag flag)
                                 (compare-and-set! intercepted false true))
                        ;; The child has read the old flag. Parent claim clears
                        ;; its strong holder while the child still owns its gate.
                        (let [claim (future (#'v2/internal-call! p #(#'v2/claim-child! p c holder)))]
                          (try (when (= ::timeout (deref claim 5000 ::timeout))
                                 (throw (ex-info "parent claim did not reach its boundary" {})))
                               (finally (future-cancel claim)))))
                      result))}
      #(v2/release-world! c))
    (v2/acknowledge-world-settlement! cap {:settled? true :value :closed})
    (pump! e)
    (let [joined? (#'v2/internal-call! p #(empty? (:children (aget ^objects p rw/W-CLOSE))))]
      {:parent p :probe (java.lang.ref.WeakReference. c)
       :joined? joined? :strong? (some? (aget ^objects holder 0))
       :claimed? (original-flag? target-flag)})))

(defn- world-collected? [^java.lang.ref.WeakReference probe]
  (loop [fuel 100]
    (System/gc)
    (if (nil? (.get probe)) true
        (if (zero? fuel) false
            (do (Thread/sleep 10) (recur (dec fuel)))))))

(deftest racing-child-promotion-cannot-retain-terminal-world-in-open-parent
  (let [{:keys [parent probe joined? strong? claimed?]} (claimed-holder-retention-fixture)]
    ;; Assert only scalars so test diagnostics cannot themselves root the child.
    (is (true? joined?))
    (is (true? claimed?))
    (is (false? strong?))
    (is (world-collected? probe))
    (is (false? (:requested? (status parent))))
    (close! parent)))
