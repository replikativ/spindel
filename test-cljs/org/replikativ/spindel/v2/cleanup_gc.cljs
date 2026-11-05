(ns org.replikativ.spindel.v2.cleanup-gc
  "Run compiled Node artifact with --expose-gc; no verify/audit retention."
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.cleanup :as cleanup]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.rows :as rw]))

(defn- until [label ready next]
  (letfn [(check [n]
            (js/gc)
            (cond
              (ready) (do (println "PASS" label) (next))
              (= n 200) (throw (ex-info "cleanup GC probe failed" {:probe label}))
              :else (js/setTimeout #(check (inc n)) 10)))]
    (js/setTimeout #(check 0) 0)))

(defn- held-result-fixture [mode]
  (let [w (v2/world) payload (js/Uint8Array. (* 1024 1024))
        weak (hs/weak payload) complete (atom nil) op (atom nil) out (atom [])]
    (binding [v2/*world* w]
      (let [t (task
               (let [resource (v2/cleanup-resource
                               (fn [cb]
                                 (reset! complete cb)
                                 (fn [] (when-not (= (* 1024 1024) (.-byteLength payload))
                                          (throw (ex-info "lost close payload" {}))))))
                     operation (v2/cleanup-operation resource)]
                 (reset! op operation)
                 (try (if (= mode :error) (throw (ex-info "body error" {})) :body)
                      (finally (v2/await-finalization operation)))))]
        (v2/value-async t (fn [v failed?] (swap! out conj [v failed?])))
        (when (= mode :cancel) (v2/cancel-task! t))
        (@complete :closed)
        {:weak weak :world w :task t :callback @complete :operation @op :out out}))))

(defn- held-results [modes next]
  (if-let [mode (first modes)]
    (let [{:keys [weak world task callback operation out]} (held-result-fixture mode)]
      (until (str "held " (name mode) " result/operation/callback releases payload")
             #(and (nil? (aget (v2/row-of task) rw/K-RUN))
                   (nil? (hs/deref-weak weak)))
             #(do
                (assert (= 1 (count @out)))
                (case mode
                  :success (assert (= [[:body false]] @out))
                  :error (assert (second (first @out)))
                  :cancel (assert (v2/cancelled? (ffirst @out))))
                (assert (nil? (aget (v2/row-of task) rw/K-BODY)))
                (assert (nil? (aget (v2/row-of task) rw/K-INPUTS)))
                (assert (= :settled (:phase (v2/cleanup-operation-status operation))))
                (callback :duplicate)
                (v2/release-world! world)
                (held-results (rest modes) next))))
    (next)))

(defn- held-operation-fixture []
  (let [w (v2/world) complete (atom nil) weak (hs/weak w)
        resource (v2/cleanup-resource w (fn [cb]
                                          (when-not (aget w rw/W-ROOT)
                                            (throw (ex-info "missing declared owner" {})))
                                          (reset! complete cb) nil))
        operation (binding [v2/*world* w] (v2/cleanup-operation resource))]
    (cleanup/subscribe! operation (fn [_] (assert (some? (aget w rw/W-ROOT)))))
    (@complete :closed)
    {:weak weak :callback @complete :operation operation}))

(defn- held-terminal-capabilities [next]
  (let [{:keys [weak callback operation]} (held-operation-fixture)]
    (until "terminal operation and held physical callback do not root world"
           #(nil? (hs/deref-weak weak))
           #(do
              (assert (= {:phase :settled :subscribers 0 :outcome [:closed false]}
                         (v2/cleanup-operation-status operation)))
              (callback :duplicate)
              (next)))))

(defn- world-close-fixture []
  (let [w (v2/world) owner (v2/world-host-owner w)
        payload (js/Uint8Array. (* 1024 1024))
        weak-world (hs/weak w) weak-payload (hs/weak payload)
        cap (v2/register-world-settlement! owner w [:acquisition])
        reservation (:acquisition (v2/world-preparations cap))]
    (v2/reset-world! w {:payload payload})
    (let [operation (v2/close-world! owner w)
          withdraw (v2/subscribe-world-close! operation (fn [_] (assert (aget w rw/W-ROOT))))]
      (v2/update-world-settlement! cap {:id :native-discard :phase :ambiguous})
      (v2/finish-world-preparation! reservation {:disposed? true})
      {:world weak-world :payload weak-payload :owner owner :cap cap
       :reservation reservation :operation operation :withdraw withdraw})))

(defn- held-world-close-controls [next]
  (let [{:keys [world payload owner cap reservation operation withdraw]} (world-close-fixture)]
    (until "pending recovery retains its exact world obligation"
           #(some? (hs/deref-weak world))
           #(do
              (assert (not (:terminal? (v2/world-close-status operation))))
              (v2/acknowledge-world-settlement! cap {:settled? true :value :physically-disposed})
              (until "held terminal owner/cap/reservation/operation/withdrawal release world and payload"
                     (fn [] (and (nil? (hs/deref-weak world)) (nil? (hs/deref-weak payload))))
                     (fn []
                       (assert (:terminal? (v2/world-close-status operation)))
                       (assert (nil? @(.-cell owner)))
                       (v2/acknowledge-world-settlement! cap {:settled? true :value :duplicate})
                       (v2/finish-world-preparation! reservation {:disposed? true})
                       (withdraw)
                       (next)))))))

(defn- private-wait-callback [payload calls]
  (fn [_ _]
    (when-not (= (* 1024 1024) (.-byteLength payload)) (throw (ex-info "lost private payload" {})))
    (swap! calls inc)))

(defn- canceled-pending-entry-fixture [kind]
  (let [p (v2/world) pubs (atom []) submit (atom []) calls (atom 0)]
    (v2/install-handlers! p {:s #(swap! pubs conj %)})
    (binding [v2/*world* p]
      (let [x (v2/signal :value) t (task (v2/savepoint :s nil)) c (v2/instantiate (first @pubs))]
        (with-redefs [v2/after-gate-action! (fn [f] (swap! submit conj f))]
          (v2/activate! c :value))
        (let [payload (js/Uint8Array. (* 1024 1024)) weak (hs/weak payload)
              callback (private-wait-callback payload calls)
              withdraw (if (= :wait kind)
                         (v2/value-async (v2/in-world c t) callback)
                         (v2/observe! (v2/in-world c x) callback))]
          (withdraw)
          {:parent p :child c :task t :submit (first @submit) :withdraw withdraw :weak weak :calls calls})))))

(defn- canceled-pending-entries [kinds next]
  (if-let [kind (first kinds)]
    (let [{:keys [parent child task submit withdraw weak calls]} (canceled-pending-entry-fixture kind)]
      (until (str "withdrawn pending " (name kind) " releases private payload before admission")
             #(nil? (hs/deref-weak weak))
             #(do
                (assert (aget child rw/W-UNBORN))
                (assert (zero? (:deferred-host (v2/world-close-status child))))
                (assert (zero? @calls))
                (submit)
                (withdraw)
                (v2/release-world! parent)
                (when-not (v2/handle? task) (throw (ex-info "lost explicit task handle" {})))
                (canceled-pending-entries (rest kinds) next))))
    (next)))

(defn -main []
  (when-not (and (exists? js/WeakRef) (exists? js/gc))
    (throw (ex-info "requires Node WeakRef and --expose-gc" {})))
  (held-results [:success :error :cancel]
                #(held-terminal-capabilities
                  (fn [] (held-world-close-controls
                          (fn [] (canceled-pending-entries [:wait :observe] (fn [] (println "CLEANUP GC OK")))))))))

(set! *main-cli-fn* -main)
