(ns org.replikativ.spindel.engine.native-custody-concurrency-test
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]])
  (:import [java.util.concurrent CountDownLatch TimeUnit]))

(deftest transfer-and-source-close-linearize-without-losing-custody
  (dotimes [iteration 32]
    (let [rt (owned/runtime {:audit? true :cps-exit? true})
          source (lifetime/open-scope! rt :source)
          destination (lifetime/open-scope! rt :destination)
          {child :context bearer :capability}
          (rtp/fork-owned-world! rt {:world-id [:w 1] :owner source})
          start (CountDownLatch. 1)
          transfer (future
                     (assert (.await start 5 TimeUnit/SECONDS))
                     (try
                       {:bearer (rtp/transfer-owned-world! rt bearer source rt destination
                                                           {:operation-id [:move iteration]})}
                       (catch Exception error {:error error})))
          close (future
                  (assert (.await start 5 TimeUnit/SECONDS))
                  (lifetime/close-scope! rt source))]
      (try
        (.countDown start)
        (let [result (deref transfer 10000 ::timeout)
              closed (deref close 10000 ::timeout)]
          (is (not= ::timeout result))
          (is (nil? closed))
          (when (and (not= ::timeout result) (not= ::timeout closed))
            (if (:bearer result)
              (do
                (is (= :live (:status (owned/snapshot child))))
                (is (= 1 (:custody-live-leaves (owned/storage-stats rt)))))
              (do
                (is (contains? #{:stale-capability :closed-execution-owner}
                               (:error (ex-data (:error result)))))
                (is (= :released (:status (owned/snapshot child))))))
            (lifetime/close-scope! rt destination)
            (is (= :released (:status (owned/snapshot child))))
            (doseq [field [:custody-live-leaves :custody-holder-buckets :custody-claims :custody-pending]]
              (is (zero? (get (owned/storage-stats rt) field)) (str field)))
            (verify-boundaries! rt)))
        (finally
          (future-cancel transfer)
          (future-cancel close))))))
