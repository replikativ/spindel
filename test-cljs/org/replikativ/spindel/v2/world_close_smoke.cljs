(ns org.replikativ.spindel.v2.world-close-smoke
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task await await-finalization]]
            [org.replikativ.spindel.v2.cleanup :as cleanup]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.rows :as rw]))

(def ^:private jobs (atom []))

(defn- manual-world []
  {:world (v2/world) :jobs jobs})

(defn- pump! [{:keys [jobs]}]
  (loop [fuel 1000]
    (when-let [job (first @jobs)]
      (assert (pos? fuel) "close did not reach a boundary")
      (swap! jobs subvec 1)
      (job)
      (recur (dec fuel)))))

(defn- status [w] (v2/world-close-status w))
(defn- close! [w] (v2/close-world! (v2/world-host-owner w) w))

(defn- native-and-preparation! []
  (let [{w :world :as e} (manual-world) owner (v2/world-host-owner w)
        cap (v2/register-world-settlement! owner w [:late])
        reservation (:late (v2/world-preparations cap)) c (v2/world)
        native (v2/register-world-settlement! (v2/world-host-owner c) c [])
        op (close! w) seen (atom [])]
    (v2/subscribe-world-close! op #(swap! seen conj %))
    (assert (not (:execution-retired? (status w))))
    (v2/finish-world-preparation! reservation {:world c})
    (pump! e)
    (assert (:execution-retired? (status w)))
    (assert (not (:terminal? (status w))))
    (v2/update-world-settlement! native {:id :native-ack :phase :ambiguous})
    (assert (= 1 (count (:recovery (status c)))))
    (v2/acknowledge-world-settlement! native {:settled? true :value :disposed})
    (pump! e)
    (v2/acknowledge-world-settlement! cap {:settled? true :value :reconciled})
    (pump! e)
    (assert (= [[nil false]] @seen))
    (assert (identical? owner (v2/world-host-owner w)))
    (assert (:terminal? (v2/world-close-status op)))
    (assert (= :settled (:phase (cleanup/status op))))))

(defn- cycle-and-error-route! [caught?]
  (let [{p :world :as e} (manual-world) child (atom nil) exited (atom false)
        error (ex-info "child-native" {})]
    (binding [v2/*world* p]
      (let [gate (v2/deferred)
            t (task
               (let [[branch c] (v2/fork)]
                 (if (= :parent branch)
                   (do (reset! child c)
                       (try (await gate)
                            (finally
                              (try (await-finalization (v2/close-world! c))
                                   (catch :default t (when-not caught? (throw t))))
                              (reset! exited true))))
                   (await gate))))]
        (pump! e)
        (let [c @child parent-native (v2/register-world-settlement! (v2/world-host-owner p) p [])
              child-native (v2/register-world-settlement! (v2/world-host-owner c) c [])]
          (v2/cancel-task! t)
          (close! p)
          (pump! e)
          (assert (:execution-retired? (status c)))
          (assert (not (:execution-retired? (status p))))
          (v2/update-world-settlement! parent-native {:id :refund-received :phase :accepted})
          (v2/update-world-settlement! child-native {:id :discard :phase :ambiguous})
          (assert (not (:terminal? (status c))))
          (v2/acknowledge-world-settlement! child-native {:settled? true :error error})
          (pump! e)
          (assert (if caught? @exited (not @exited)))
          (assert (:execution-retired? (status p)))
          (v2/acknowledge-world-settlement! parent-native {:settled? true :value :disposed})
          (pump! e)
          (assert (:terminal? (status p)))
          (assert (= (if caught? [] [error])
                     (vec (:spindel/cleanup-failures (ex-data (first (:outcome (status p)))))))))))))

(defn- fork-unborn! []
  (let [{w :world :as e} (manual-world) pubs (atom []) fins (atom 0)]
    (v2/install-handlers! w {:s #(swap! pubs conj %)})
    (binding [v2/*world* w]
      (let [t (task (try (v2/savepoint :s nil) (finally (swap! fins inc))))
            c (v2/instantiate (first @pubs)) owner (v2/world-host-owner c)
            cap (v2/register-world-settlement! owner c [])]
        (assert (aget c rw/W-UNBORN))
        (close! c)
        (pump! e)
        (assert (:execution-retired? (status c)))
        (assert (not (:terminal? (status c))))
        (assert (zero? @fins))
        (v2/acknowledge-world-settlement! cap {:settled? true :value :native-disposed})
        (assert (:terminal? (status c)))
        (assert (not (identical? owner (v2/world-host-owner w))))
        (v2/abandon! (first @pubs))
        (pump! e)
        (assert (= 1 @fins))
        (v2/release! t)))))

(defn- queued-activation-barrier! []
  (let [{p :world :as e} (manual-world) pubs (atom []) seen (atom []) result (atom []) canceled (atom [])]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (let [x (v2/signal :before) t (task (v2/savepoint :s nil))
            c (v2/instantiate (first @pubs)) local-x (v2/in-world c x) local-t (v2/in-world c t)]
        (aset c rw/W-INLINE false)
        (v2/activate! c :value)
        (assert (nil? (aget c rw/W-ACTIVATION)))
        (v2/write! local-x :after)
        (v2/observe! local-x (fn [v failed?] (swap! seen conj [v failed?])))
        (let [withdraw (v2/value-async local-t (fn [v failed?] (swap! canceled conj [v failed?])))] (withdraw))
        (v2/value-async local-t (fn [v failed?] (swap! result conj [v failed?])))
        (assert (empty? @seen))
        (pump! e)
        (assert (= [[:after false]] @seen))
        (assert (= [[:value false]] @result))
        (assert (empty? @canceled))
        (close! p)
        (pump! e)
        (assert (:terminal? (aget p rw/W-CLOSE)))
        (assert (:terminal? (aget c rw/W-CLOSE)))))))

(defn- refused-synchronous-controls! []
  (let [{w :world :as e} (manual-world) owner (v2/world-host-owner w)]
    (aset w rw/W-INLINE false)
    (assert (try (v2/register-world-settlement! owner w [:orphan]) false (catch :default _ true)))
    (pump! e)
    (assert (empty? (:settlements (aget w rw/W-CLOSE))))
    (assert (empty? (:preparations (aget w rw/W-CLOSE))))
    (assert (try (v2/close-world! owner w) false (catch :default _ true)))
    (pump! e)
    (assert (not (:requested? (aget w rw/W-CLOSE))))
    (aset w rw/W-INLINE true)
    (let [cap (v2/register-world-settlement! owner w [:a])
          reservation (:a (v2/world-preparations cap))]
      (aset w rw/W-INLINE false)
      (assert (try (v2/update-world-settlement! cap {:id :late :phase :ambiguous}) false (catch :default _ true)))
      (assert (try (v2/finish-world-preparation! reservation {:disposed? true}) false (catch :default _ true)))
      (pump! e)
      (assert (= 1 (count (:preparations (aget w rw/W-CLOSE)))))
      (assert (every? (fn [debt] (nil? (:recovery debt))) (vals (:settlements (aget w rw/W-CLOSE)))))
      (v2/release-world! w)
      (pump! e)
      (assert (not (:execution-retired? (aget w rw/W-CLOSE))))
      (aset w rw/W-INLINE true)
      (v2/finish-world-preparation! reservation {:disposed? true})
      (assert (:execution-retired? (aget w rw/W-CLOSE)))
      (aset w rw/W-INLINE false)
      (assert (try (v2/acknowledge-world-settlement! cap {:settled? true :value :must-not-commit}) false (catch :default _ true)))
      (pump! e)
      (assert (= 1 (count (:settlements (aget w rw/W-CLOSE)))))
      (assert (not (:terminal? (aget w rw/W-CLOSE))))
      (aset w rw/W-INLINE true)
      (v2/acknowledge-world-settlement! cap {:settled? true :value :physically-closed})
      (assert (:terminal? (aget w rw/W-CLOSE))))))

(defn- replay-failure-and-budget! []
  (let [{p :world :as e} (manual-world) pubs (atom []) submit (atom []) result (atom []) effects (atom [])]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (let [t (task (v2/savepoint :s nil)) c (v2/instantiate (first @pubs))]
        (with-redefs [v2/after-gate-action! (fn [f] (swap! submit conj f))]
          (v2/activate! c :value))
        (v2/host! c #(throw (ex-info "queued body" {})))
        (v2/host! c #(swap! effects conj :after-throw))
        (v2/value-async (v2/in-world c t) (fn [v failed?] (swap! result conj [v failed?])))
        (doseq [f @submit] (f))
        (pump! e)
        (assert (= [:after-throw] @effects))
        (assert (= [[:value false]] @result))
        (close! p)
        (pump! e))))
  (let [{p :world :as e} (manual-world) pubs (atom []) submit (atom []) effects (atom [])]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (task (v2/savepoint :s nil))
      (let [c (v2/instantiate (first @pubs)) cap (v2/register-world-settlement! (v2/world-host-owner c) c [])]
        (aset c rw/W-BUDGET 2)
        (with-redefs [v2/after-gate-action! (fn [f] (swap! submit conj f))]
          (v2/activate! c :value))
        (dotimes [i 12] (v2/host! c #(swap! effects conj i)))
        (doseq [f @submit] (f))
        (assert (<= (count @effects) 2))
        (let [before (count @effects)]
          (v2/release-world! c)
          (v2/acknowledge-world-settlement! cap {:settled? true :value :closed})
          (pump! e)
          (assert (= before (count @effects)))
          (assert (:terminal? (aget c rw/W-CLOSE))))
        (close! p)
        (pump! e)))))

(defn- preactivation-fifo! []
  (let [{p :world :as e} (manual-world) pubs (atom []) before (atom []) after (atom [])]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (let [x (v2/signal :before) t (task (v2/savepoint :s nil)) c (v2/instantiate (first @pubs))]
        (aset c rw/W-INLINE false)
        (v2/write! (v2/in-world c x) :preactivate)
        (v2/value-async (v2/in-world c t) (fn [v failed?] (swap! before conj [v failed?])))
        (v2/activate! c :value)
        (v2/value-async (v2/in-world c t) (fn [v failed?] (swap! after conj [v failed?])))
        (pump! e)
        (assert (:spindel/unborn (ex-data (ffirst @before))))
        (assert (= [[:value false]] @after))
        (close! p)
        (pump! e)))))

(defn -main []
  (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))]
    (native-and-preparation!)
    (cycle-and-error-route! true)
    (cycle-and-error-route! false)
    (fork-unborn!)
    (queued-activation-barrier!)
    (refused-synchronous-controls!)
    (replay-failure-and-budget!)
    (preactivation-fifo!)
    (println "WORLD CLOSE SMOKE OK")))

(set! *main-cli-fn* -main)
