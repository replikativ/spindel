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

(defn -main []
  (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))]
    (native-and-preparation!)
    (cycle-and-error-route! true)
    (cycle-and-error-route! false)
    (fork-unborn!)
    (println "WORLD CLOSE SMOKE OK")))

(set! *main-cli-fn* -main)
