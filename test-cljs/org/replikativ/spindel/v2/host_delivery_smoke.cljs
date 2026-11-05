(ns org.replikativ.spindel.v2.host-delivery-smoke
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [taoensso.trove :as trove]))

(def failures (atom []))
(def jobs (atom []))
(def executor (js-obj))
(defn- check! [label value]
  (when-not value (swap! failures conj label) (println "FAIL" label)))
(defn- outcome [f] (try [(f) false] (catch :default error [error true])))
(defn- pump-one! [] (when-let [f (first @jobs)] (swap! jobs subvec 1) (f) true))
(defn- pump! [] (loop [n 1000] (when (pump-one!) (assert (pos? n)) (recur (dec n)))))
(defn- world [] (v2/world {:executor executor :verify? true}))
(defn- close! [p] (v2/release-world! p) (pump!))
(defn- recorder [events]
  (fn [_ _ level id lazy-data]
    (when (#{:engine/host-call-turn-failed :engine/host-handoff-failed} id)
      (swap! events conj [level id (:error (:data (force lazy-data)))]))))

(defn- falsy-outcomes! []
  (doseq [value [nil false] failed? [false true]]
    (let [p (world)]
      (check! [:falsy value failed?]
              (= [value failed?] (outcome #(v2/call-in! p (fn [] (if failed? (throw value) value))))))
      (close! p))))

(defn- committed-outcomes! []
  (doseq [value [nil false :unique] failed? [false true]]
    (let [p (world) x (v2/signal p 0) late (ex-info "later observer" {}) own (ex-info "own failure" {})
          events (atom []) ran (atom 0)
          withdraw (v2/observe! x (fn [v failed?] (when (and (= 1 v) (not failed?))
                                                    (swap! ran inc) (throw late))))]
      (binding [trove/*log-fn* (recorder events)]
        (check! [:owned-outcome value failed?]
                (= [(if failed? own value) failed?]
                   (outcome #(v2/call-in! p (fn [] (v2/reset-world! p {:committed true})
                                              (v2/write! x 1) (if failed? (throw own) value))))))
        (check! [:reported value failed?] (= [[:error :engine/host-call-turn-failed late]] @events)))
      (check! :committed-marker (= {:committed true} (aget p rw/W-STATE)))
      (check! :callback-once (= 1 @ran)) (withdraw) (close! p))))

(defn- callback-suffix! []
  (doseq [queued? [false true] fail-at [0 1 2]]
    (let [p (world) x (v2/signal p 0) y (v2/signal p :new) seen (atom []) extra (atom nil)
          error (ex-info "batch failure" {})
          withdraws (mapv (fn [i] (v2/observe! x (fn [v failed?]
                                                   (when (and (= 1 v) (not failed?))
                                                     (swap! seen conj i)
                                                     (when (= i fail-at)
                                                       (reset! extra (v2/observe! y (fn [v _] (swap! seen conj v))))
                                                       (v2/send-world! p #(v2/reset-world! p {:queued true}))
                                                       (throw error)))))) (range 3))]
      (assert (empty? @jobs))
      (check! [:original-error queued? fail-at]
              (= [error true] (if queued?
                                (do (v2/send-world! p #(v2/write! x 1)) (outcome pump-one!))
                                (outcome #(v2/write! x 1)))))
      (check! [:consumed-prefix queued? fail-at] (= (vec (range (inc fail-at))) @seen))
      (check! [:scheduled-without-rescue queued? fail-at] (seq @jobs))
      (pump!)
      (check! [:suffix-fifo queued? fail-at] (= [0 1 2 :new] @seen))
      (check! [:parent-work queued? fail-at] (= {:queued true} (aget p rw/W-STATE)))
      (doseq [f withdraws] (f)) (when-let [f @extra] (f)) (close! p))))

(defn- unsupported-and-preclaim! []
  (doseq [preclaim? [false true]]
    (let [p (world) ran (atom 0) error (ex-info "earlier ingress" {})]
      (if preclaim? (v2/send-world! p #(throw error)) (aset p rw/W-INLINE false))
      (let [[actual failed?] (outcome #(v2/call-in! p (fn [] (swap! ran inc) (v2/reset-world! p {:late true}))))]
        (check! [:refusal preclaim?] failed?)
        (when preclaim? (check! :preclaim-original (identical? actual error))))
      (pump!)
      (check! [:no-latent-run preclaim?] (zero? @ran))
      (check! [:no-latent-state preclaim?] (= {} (aget p rw/W-STATE)))
      (aset p rw/W-INLINE true) (close! p))))

(defn- activation! []
  (doseq [accept? [false true]]
    (let [p (world) pubs (atom []) pending (atom []) ran (atom 0) original v2/internal!]
      (v2/install-handlers! p {:s #(swap! pubs conj %)})
      (binding [v2/*world* p]
        (task (v2/savepoint :s nil))
        (let [c (v2/instantiate (first @pubs))]
          ;; Actual child claim is published; only original parent's admission
          ;; closure is held. Intent grants no permission to execute our body.
          (with-redefs [v2/internal! (fn [w f] (if (identical? p w)
                                                 (swap! pending conj #(original w f))
                                                 (original w f)))]
            (v2/activate! c :go))
          (assert (some? (:identity (aget c rw/W-ACTIVATION))))
          (let [[_ failed?] (outcome #(v2/call-in! c (fn [] (swap! ran inc))))]
            (check! [:deferred-refusal accept?] failed?))
          (when-not accept? (v2/release-world! p))
          (doseq [f @pending] (f)) (pump!)
          (check! [:canceled-replay accept?] (zero? @ran))
          (close! p))))))

(defn- owned-rejection! []
  (let [p (world) ran (atom 0)]
    (v2/send-world! p #(v2/release-world! p))
    (let [[error failed?] (outcome #(v2/call-in! p (fn [] (swap! ran inc))))]
      (check! :rejected-outcome failed?)
      (check! :released-identity (:spindel/released (ex-data error)))
      (check! :rejected-never-runs (zero? @ran)))
    (pump!)))

(defn- immediate-and-refused-handoff! []
  (doseq [refuse? [false true]]
    (let [p (world) x (v2/signal p 0) original hs/execute! seen (atom []) submissions (atom []) events (atom [])
          primary (ex-info "original callback" {}) secondary (ex-info "nested turn or rejected submission" {})
          a (v2/observe! x (fn [v _] (when (= 1 v) (swap! seen conj :a) (throw primary))))
          b (v2/observe! x (fn [v _] (when (= 1 v) (swap! seen conj :b) (throw secondary))))
          c (v2/observe! x (fn [v _] (when (= 1 v) (swap! seen conj :c))))]
      (binding [trove/*log-fn* (recorder events)]
        (with-redefs [hs/execute! (fn [e f]
                                    (if (identical? e executor)
                                      (do (swap! submissions conj [(hs/held? (aget p rw/W-LOCK)) (v2/cw)])
                                          (if refuse? (throw secondary) (f)))
                                      (original e f)))]
          (check! [:handoff-primary refuse?] (= [primary true] (outcome #(v2/write! x 1))))
          (check! [:handoff-secondary refuse?] (= [[:error :engine/host-handoff-failed secondary]] @events))))
      (check! [:unlocked-submission refuse?] (and (seq @submissions) (every? #{[false nil]} @submissions)))
      (check! [:immediate-order refuse?] (= (if refuse? [:a] [:a :b :c]) @seen))
      (when refuse?
        (check! :refused-scheduled-limit (hs/flag? (aget p rw/W-SCHEDULED)))
        ;; Teardown rescue only, after all scheduling/error assertions.
        (outcome #(v2/host! p (fn [] nil))))
      (a) (b) (c) (close! p))))

(defn -main []
  (let [original hs/execute!]
    (with-redefs [hs/execute! (fn [e f] (if (identical? e executor) (swap! jobs conj f) (original e f)))]
      (falsy-outcomes!) (committed-outcomes!) (callback-suffix!)
      (unsupported-and-preclaim!) (activation!) (owned-rejection!) (immediate-and-refused-handoff!)
      (if (seq @failures)
        (throw (ex-info "host delivery behavioral assertions failed" {:failures @failures}))
        (println "HOST DELIVERY SMOKE OK")))))
(set! *main-cli-fn* -main)
