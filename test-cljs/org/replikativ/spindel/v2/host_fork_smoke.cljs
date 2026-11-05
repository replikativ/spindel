(ns org.replikativ.spindel.v2.host-fork-smoke
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task spin await await-finalization]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.lifetime :as lt]))
(def jobs (atom []))
(defn- pump! [] (loop [n 1000] (when-let [f (first @jobs)] (assert (pos? n)) (swap! jobs subvec 1) (f) (recur (dec n)))))
(defn- snapshot [w]
  {:rank @v2/world-order :next-id (v2/peek-id w)
   :worlds (:worlds (lt/census (aget w rw/W-FAMILY) (aget w rw/W-WATCHES) nil))
   :acquisition (:next-child (aget w rw/W-CLOSE))
   :owned (some-> (aget w rw/W-OWNED) hs/msize)
   :fork-host (count (filter #(= :fork-host (first (:item %))) (array-seq (aget w rw/W-LOG))))})

(defn- close! [w] (v2/release-world! w))
(defn- failure [f] (try (f) nil (catch :default e e)))
(defn- attempt [p failures] (swap! failures conj (failure #(v2/fork! p))))

(defn- noninline-refusal! []
  (let [p (v2/world {:inline? false :verify? true}) before (snapshot p) epoch (aget p rw/W-EPOCH)
        error (failure #(v2/fork! p))]
    (assert (= :world-control (:spindel/invalid (ex-data error))))
    (assert (= before (snapshot p)))
    (pump!)
    (assert (= before (snapshot p)))
    (assert (identical? epoch (aget p rw/W-EPOCH)))
    ;; Later ordinary activation and close cannot revive a canceled allocation.
    (v2/host! p (fn [] nil)) (close! p) (pump!)
    (assert (= 0 (:fork-host (snapshot p))))
    (assert (= (:rank before) (:rank (snapshot p))))
    (assert (= (:next-id before) (:next-id (snapshot p))))))

(defn- inline-cow! []
  (let [p (v2/world {:verify? true})]
    (binding [v2/*world* p]
      (let [x (v2/signal 1) c (v2/fork! p) cx (v2/in-world c x)]
        (assert (= 1 (v2/value cx)))
        (v2/write! x 2) (assert (= 1 (v2/value cx)))
        (v2/write! cx 3) (assert (= 2 (v2/value x)))
        (assert (= 3 (v2/value cx)))
        (assert (nil? (aget (aget c rw/W-HOLDER) 0)))
        (assert (= 1 (:fork-host (snapshot p))))
        (close! p) (pump!)))))

(defn- callback-handoff! []
  (doseq [queued? [false true] throws? [false true]]
    (with-redefs [hs/execute! (if queued? (fn [_ f] (swap! jobs conj f)) (fn [_ f] (f)))]
      (let [p (v2/world) marker (atom false) child (atom nil) work (atom []) handoffs (atom [])
            original-handoff v2/handoff!]
        (binding [v2/*world* p]
          (let [gate (v2/deferred) x (v2/signal 0)
                worker (task (await gate)
                             (when-not (identical? p (v2/current-world))
                               (swap! work conj [@marker (hs/held? (aget p rw/W-LOCK))])))
                withdraw (v2/observe! x (fn [value failed?]
                                          (when (and (not failed?) (= 1 value))
                                            (reset! marker true)
                                            (try (v2/deliver! gate :go)
                                                 (reset! child (v2/fork! p))
                                                 (assert (hs/held? (aget p rw/W-LOCK)))
                                                 (assert (some? (aget @child rw/W-HOLDER)))
                                                 (when throws? (throw (ex-info "callback after allocation" {})))
                                                 (finally (reset! marker false))))))]
            (with-redefs [v2/handoff! (fn [w]
                                        (when-not (identical? p w)
                                          (swap! handoffs conj [@marker (hs/held? (aget p rw/W-LOCK))]))
                                        (original-handoff w))]
              (assert (= throws? (some? (failure #(v2/write! x 1)))))
              (pump!))
            (assert (seq @handoffs))
            (assert (every? #{[false false]} @handoffs))
            (assert (= [[false false]] @work))
            (let [c @child cap (v2/register-world-settlement! (v2/world-host-owner c) c [])]
              (close! p) (pump!)
              (assert (= 1 (:child-terminal (v2/world-close-status p))))
              (v2/acknowledge-world-settlement! cap {:settled? true :value :closed})
              (pump!) (assert (:terminal? (v2/world-close-status p))))
            (withdraw)))))))

(defn- forbidden-contexts! []
  (let [p (v2/world {:verify? true}) q (v2/world) failures (atom []) before (snapshot p)]
    (binding [v2/*world* p]
      (task (attempt p failures))
      (v2/value (spin (attempt p failures)))
      (task (try :body (finally (attempt p failures))))
      (task (let [r (v2/cleanup-resource (fn [cb] (attempt p failures) (cb :closed) nil))]
              (try :body (finally (await-finalization (v2/cleanup-operation r))))))
      (v2/host! q #(attempt p failures))
      (assert (= 5 (count @failures)))
      (assert (every? some? @failures))
      (assert (= (:rank before) (:rank (snapshot p))))
      (assert (= 0 (:fork-host (snapshot p))))
      (assert (nil? (aget p rw/W-OWNED))))
    (doseq [invalid [nil {} [] (array)]] (assert (some? (failure #(v2/fork! invalid)))))
    (let [child (atom nil)] (v2/host! p #(reset! child (v2/fork! p))) (assert (some? @child)))
    (close! p) (close! q) (pump!)))

(defn- capacity-and-lifecycle! []
  (let [p (v2/world {:verify? true})]
    (aset p rw/W-CLOSE (assoc (aget p rw/W-CLOSE) :next-child [4294967295 4294967295]))
    (let [before (snapshot p) epoch (aget p rw/W-EPOCH)]
      (assert (= :world-acquisition-order-exhausted
                 (:spindel/invalid (ex-data (failure #(v2/fork! p))))))
      (assert (= before (snapshot p)))
      (assert (identical? epoch (aget p rw/W-EPOCH))))
    (close! p)
    (pump!))
  (let [p (v2/world {:verify? true}) before (snapshot p) epoch (aget p rw/W-EPOCH)
        isolated (atom [4294967295 4294967295])]
    (with-redefs [v2/world-order isolated]
      (assert (= :world-order-exhausted
                 (:spindel/invalid (ex-data (failure #(v2/fork! p)))))))
    (assert (= [4294967295 4294967295] @isolated))
    (assert (= before (snapshot p)))
    (assert (identical? epoch (aget p rw/W-EPOCH)))
    (close! p)
    (pump!))
  (let [p (v2/world {:verify? true})]
    (close! p)
    (pump!)
    (let [before (snapshot p)]
      (assert (:spindel/released (ex-data (failure #(v2/fork! p)))))
      (assert (= before (snapshot p))))))

(defn- unborn! []
  (doseq [phase [:before-intent :intent :claim]]
    (let [p (v2/world) pubs (atom []) pending (atom []) original-internal v2/internal!]
      (v2/install-handlers! p {:s #(swap! pubs conj %)})
      (binding [v2/*world* p]
        (let [t (task (v2/savepoint :s nil)) c (v2/instantiate (first @pubs))]
          (case phase
            :before-intent nil
            :intent (with-redefs [v2/after-gate-action! #(swap! pending conj %)] (v2/activate! c :go))
            :claim (with-redefs [v2/internal! (fn [w f] (if (identical? p w)
                                                          (swap! pending conj #(original-internal p f))
                                                          (original-internal w f)))] (v2/activate! c :go)))
          (let [before (snapshot c) epoch (aget c rw/W-EPOCH)]
            (assert (some? (failure #(v2/fork! c))))
            (assert (= before (snapshot c))) (assert (identical? epoch (aget c rw/W-EPOCH)))
            (doseq [f @pending] (f))
            (when (= phase :before-intent) (v2/activate! c :go))
            (pump!)
            (assert (= (:rank before) (:rank (snapshot c))))
            (assert (= 0 (:fork-host (snapshot c))))
            (assert (nil? (aget c rw/W-OWNED))))
          (close! p) (pump!))))))

(defn- result-callback! []
  (let [p (v2/world) child (atom nil)]
    (binding [v2/*world* p]
      (v2/value-async (task :ready)
                      (fn [_ failed?]
                        (assert (not failed?))
                        (assert (hs/held? (aget p rw/W-LOCK)))
                        (reset! child (v2/fork! p))))
      (assert (some? @child))
      (close! p)
      (pump!))))

(defn -main []
  (with-redefs [hs/execute! (fn [_ f] (swap! jobs conj f))]
    (noninline-refusal!)
    (inline-cow!)
    (callback-handoff!)
    (forbidden-contexts!)
    (result-callback!)
    (capacity-and-lifecycle!)
    (unborn!)
    (println "HOST FORK SMOKE OK")))
(set! *main-cli-fn* -main)
