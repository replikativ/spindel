(ns org.replikativ.spindel.ygg-stamp-retry-portable-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [yggdrasil.convergent :as yc]
            [yggdrasil.convergent.gset :as g]))

(defn- check-fail-once-stamp-retry [copy?]
  (let [parent (context/create-execution-context)
        calls (atom 0)
        stamped (atom [])]
    (try
      (binding [ec/*execution-context* parent]
        (ygg/register!
         (g/gset "book" {:store-config {:backend :memory :id (random-uuid)}} {:sync? true})
         {:grade :linear
          :intents (fn [{:keys [system-id child-ctx]}]
                     (binding [ec/*execution-context* child-ctx]
                       (mapv (fn [x] {:intent/id x :footprint #{x}})
                             (g/elements (ygg/system system-id) {:sync? true}))))
          :stamp (fn [{:keys [contributions]}]
                   (when (= 1 (swap! calls inc))
                     (throw (ex-info "writer unavailable once" {})))
                   (swap! stamped into (mapcat :intents contributions)))})
        (let [source (ygg/fork! {:sync? true})
              [handle loser] (if copy?
                               (ygg/copy-fork! source 2 {:sync? true})
                               [source nil])]
          (binding [ec/*execution-context* (:child-ctx handle)]
            (swap! (ygg/system-signal "book") #(g/conj % :draft {:sync? true})))
          ;; Contribution collection calls fork-diff, which uses default-opts.
          ;; Only the initial synchronous merge needs this setup; retry uses CLJS defaults.
          (let [error (with-redefs [yc/default-opts (assoc yc/default-opts :sync? true)]
                        (try (ygg/merge-fork! handle {:sync? true}) nil
                             (catch #?(:clj Throwable :cljs :default) error
                               (assoc (ex-data error) :exception error))))
                pending (:pending error)]
            (is (= ::ygg/stamp-failed (:type error)) (str (:exception error)))
            (is (some? pending))
            (is (= :incomplete (:status (ygg/fork-disposition handle))))
            (is (= 1 @calls))
            (is (empty? @stamped))
            (is (= #{pending} (set (keys (rtp/get-state parent [:world/ephemeral ::ygg/pending-stamps])))))
            (when copy?
              (is (= :failed (:status (ygg/copy-family handle))))
              (is (= :incomplete (:fork/status (ygg/copied-descriptor handle (:fork-id source))))))
            ;; Keep CLJS defaults unchanged; exercise the same retry default on the JVM.
            (with-redefs [yc/default-opts #?(:clj (assoc yc/default-opts :sync? false)
                                             :cljs yc/default-opts)]
              (is (false? (:sync? yc/default-opts)))
              (is (= [pending] (ygg/retry-stamps! parent))))
            (is (= :merged (:status (ygg/fork-disposition handle))))
            (is (= 2 @calls))
            (is (= [{:intent/id :draft :footprint #{:draft}}] @stamped))
            (is (empty? (rtp/get-state parent [:world/ephemeral ::ygg/pending-stamps])))
            (is (= [] (ygg/retry-stamps!)))
            (is (= 2 @calls))
            (when copy?
              (is (= :merged (:status (ygg/copy-family handle))))
              (is (= :merged (:fork/status (ygg/copied-descriptor handle (:fork-id source)))))
              (is (nil? (:resume @(:family handle))))
              (ygg/discard-fork! loser {:sync? true})))))
      (finally (context/close-context! parent)))))

(deftest single-fork-fail-once-stamp-retries-under-cljs-defaults
  (check-fail-once-stamp-retry false))

(deftest winning-copy-fail-once-stamp-retries-under-cljs-defaults
  (check-fail-once-stamp-retry true))

(deftest retry-index-is-never-inherited-or-snapshotted
  (let [parent (context/create-execution-context)
        calls (atom 0)
        plan {:parent-ctx parent :retry #(swap! calls inc)}]
    (try
      (rtp/swap-state! parent [:world/ephemeral ::ygg/pending-stamps] (constantly {:retry plan}))
      (let [children (mapv #(context/fork-context parent :mode %) [:following :frozen])
            snapshot (context/snapshot-context parent :clean-in-flight? false)
            restored (context/restore-snapshot snapshot :drain-events? false)]
        (doseq [ctx (conj children restored)]
          (is (empty? (rtp/get-state ctx [:world/ephemeral ::ygg/pending-stamps])))
          (is (= [] (ygg/retry-stamps! ctx))))
        (is (zero? @calls))
        (is (= [:retry] (ygg/retry-stamps! parent)))
        (is (= 1 @calls))
        (doseq [ctx (conj children snapshot)]
          (is (empty? (get (rtp/get-state ctx []) :world/ephemeral)))))
      (finally (context/close-context! parent)))))

(deftest winning-copy-callback-cannot-change-terminal-family-state
  (let [parent (context/create-execution-context)
        calls (atom 0)]
    (try
      (binding [ec/*execution-context* parent]
        (let [[winner loser] (ygg/copy-fork! (ygg/fork! {:sync? true}) 2 {:sync? true})
              opts {:sync? true
                    :on-merge (fn [_]
                                (swap! calls inc)
                                (throw (ex-info "callback" {:type ::callback})))}]
          (is (= ::callback
                 (try (ygg/merge-fork! winner opts) nil
                      (catch #?(:clj Throwable :cljs :default) error (:type (ex-data error))))))
          (is (= :merged (:status (ygg/copy-family winner))))
          (is (= :merged (:fork/status (ygg/copied-descriptor
                                        winner (ygg/copied-from winner (:fork-id winner))))))
          (is (= :failed (:callback-status (ygg/fork-disposition winner))))
          (is (map? (ygg/merge-fork! winner opts)))
          (is (= 1 @calls))
          (ygg/discard-fork! loser {:sync? true})
          (is (= :merged (:status (ygg/copy-family winner))))
          (is (nil? (:resume @(:family winner))))))
      (finally (context/close-context! parent)))))

(deftest explicit-retry-context-refuses-a-foreign-plan
  (let [parent (context/create-execution-context)
        calls (atom 0)
        entry {:retry {:parent-ctx parent :retry #(swap! calls inc)}}]
    (try
      (rtp/swap-state! parent [:world/ephemeral ::ygg/pending-stamps] (constantly entry))
      ;; Even an explicitly installed foreign entry cannot execute in this world.
      (let [foreign (context/fork-context parent :state-updates {:world/ephemeral {::ygg/pending-stamps entry}})]
        (is (= [] (ygg/retry-stamps! foreign)))
        (is (zero? @calls))
        (rtp/swap-state! foreign [:world/ephemeral ::ygg/pending-stamps] (constantly nil)))
      (is (= [:retry] (ygg/retry-stamps! parent)))
      (is (= 1 @calls))
      (finally (context/close-context! parent)))))

(deftest serialized-world-drops-executable-state-and-preserves-unrelated-data
  (let [parent (context/create-execution-context)
        calls (atom 0)]
    (try
      (rtp/swap-state! parent [:roundtrip/marker] (constantly {:keep [1 2 3]}))
      (rtp/swap-state! parent [:world/ephemeral]
                       (constantly {::ygg/pending-stamps
                                    {:retry {:parent-ctx parent :retry #(swap! calls inc)}}
                                    ::other-executable #(swap! calls inc)}))
      (let [serialized (context/serialize-context parent)]
        (is (not (re-find #"world/ephemeral|pending-stamps|#object|#function" serialized)))
        (let [decoded (context/deserialize-context serialized (:executor parent))
              restored (context/restore-snapshot decoded :drain-events? false)]
          (doseq [ctx [decoded restored]]
            (is (= {:keep [1 2 3]} (rtp/get-state ctx [:roundtrip/marker])))
            (is (nil? (rtp/get-state ctx [:world/ephemeral]))))
          (is (= [] (ygg/retry-stamps! restored)))
          (is (zero? @calls))))
      (is (= [:retry] (ygg/retry-stamps! parent)))
      (is (= 1 @calls))
      (finally (context/close-context! parent)))))
