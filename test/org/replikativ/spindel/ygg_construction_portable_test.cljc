(ns org.replikativ.spindel.ygg-construction-portable-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.yggdrasil.construction :as c]
            [org.replikativ.spindel.yggdrasil.construction-test :as fixtures]
            [org.replikativ.spindel.test-helpers :refer [async]]
            [yggdrasil.protocols :as p])
  #?(:cljs (:require-macros [org.replikativ.spindel.test-helpers :refer [async]])))

(defrecord FailingSystem [id calls live cleanups failure]
  p/SystemIdentity
  (system-id [_] id)
  (system-type [_] :construction-probe)
  (capabilities [_] {:snapshotable true :overlayable true})
  p/Snapshotable
  (snapshot-id [_] "basis")
  (parent-ids [_] #{})
  (as-of [_ _] nil)
  (as-of [_ _ _] nil)
  (snapshot-meta [_ _] nil)
  (snapshot-meta [_ _ _] nil)
  p/Overlayable
  (overlay [this _]
    (if (= 2 (swap! calls inc))
      (throw failure)
      (do (swap! live conj id)
          (fixtures/->NativeOverlay this (atom this) :frozen id live cleanups (atom false))))))

(deftest async-public-fork-failure-cleans-its-ack-and-preserves-its-owner
  (async done
         (let [ctx (sp/create-execution-context) calls (atom 0) live (atom #{}) cleanups (atom [])
               failure (ex-info "Injected native constructor failure before allocation" {})
               finish! (fn [] (context/stop-context! ctx) (done))
               reject! (fn [error] (is false (str "Unexpected error: " error)) (finish!))]
           (binding [ec/*execution-context* ctx]
             (doseq [id ["a" "b"]] (ygg/register! (->FailingSystem id calls live cleanups failure)))
             ((ygg/fork! {:sync? false :mode :frozen})
              (fn [_] (is false "Fork must fail") (finish!))
              (fn [error]
                (let [owner (:construction/owner (ex-data error))
                      uncertain (filter #(= :uncertain (:phase %)) (:receipts (c/info owner)))]
                  (is (= 2 @calls))
                  (is (empty? @live))
                  (is (= 1 (count @cleanups)))
                  (is (= 1 (count uncertain)))
                  (is (= ::ygg/construction-incomplete (:type (ex-data error))))
             ;; This fixture knows the injected second hook allocated nothing.
                  (c/resolve-uncertain! owner (:id (first uncertain)) :not-acquired)
                  ((c/dispose! owner {:sync? false})
                   (fn [_] (is (= :closed (:status (c/info owner)))) (finish!))
                   reject!))))))))
