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
    (v2/host! w #(try (v2/signal w :late)
                      (catch Throwable t (reset! refused t))))
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
