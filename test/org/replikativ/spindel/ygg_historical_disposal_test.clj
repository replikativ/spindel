(ns org.replikativ.spindel.ygg-historical-disposal-test
  "Native disposal acknowledgement, independent of filesystem/provider work."
  (:require [clojure.test :refer [deftest is]]
            [is.simm.partial-cps.async :as pcps]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [yggdrasil.protocols :as p]))

(declare ->HeldOverlay)

(defrecord ProbeSystem [callbacks calls]
  p/SystemIdentity
  (system-id [_] "held-historical-disposal")
  (system-type [_] :test)
  (capabilities [_] {:snapshotable true :overlayable true :snapshot-overlay true})
  p/Snapshotable
  (snapshot-id [_] "A")
  (parent-ids [_] #{})
  (as-of [this _] this)
  (as-of [this _ _] this)
  (snapshot-meta [_ _] {})
  (snapshot-meta [_ _ _] {})
  p/Overlayable
  (overlay [this _] (->HeldOverlay this (atom this) :frozen callbacks calls))
  (advance! [this] this)
  (advance! [this _] this)
  (peek-parent [this] this)
  (peek-parent [this _] this)
  (base-ref [_] "A")
  (overlay-writes [_] {})
  (merge-down! [this] this)
  (merge-down! [this _] this)
  (discard! [_] nil)
  (discard! [_ _] nil))

(defn- held-discard [callbacks calls]
  (swap! calls inc)
  (fn [ok error]
    (reset! callbacks {:ok ok :error error})))

(defrecord HeldOverlay [parent local-writes mode callbacks calls]
  p/Overlayable
  (overlay [this _] this)
  (advance! [this] this)
  (advance! [this _] this)
  (peek-parent [_] parent)
  (peek-parent [_ _] parent)
  (base-ref [_] "A")
  (overlay-writes [_] {})
  (merge-down! [_] parent)
  (merge-down! [_ opts]
    (if (false? (:sync? opts))
      (fn [ok _] (ok parent))
      parent))
  (discard! [_] (held-discard callbacks calls))
  (discard! [_ _] (held-discard callbacks calls)))

(defn- disposal-case! [operation reject?]
  (let [root (context/create-execution-context)
        callbacks (atom nil)
        calls (atom 0)
        outcome (atom [])
        fork* (atom nil)
        released? (atom false)
        failure (ex-info "native disposal refused" {})]
    (try
      (binding [ec/*execution-context* root
                pcps/*in-trampoline* false]
        (ygg/register! (->ProbeSystem callbacks calls))
        (let [fork (ygg/fork! {:snapshots {"held-historical-disposal" "A"}})
              settle! (case operation :discard ygg/discard-fork! :merge ygg/merge-fork!)]
          (reset! fork* fork)
          ((settle! fork {:sync? false :force true})
           #(swap! outcome conj [:ok %])
           #(swap! outcome conj [:error %]))
          (is (= 1 @calls) "The real ForkHandle reached native disposal once")
          (is (= #{:ok :error} (set (keys @callbacks)))
              "The returned native CPS was actually entered, not dropped")
          (is (empty? @outcome) "Settlement cannot report success before disposal ACK")
          (is (not (#{:discarded :merged} (:status (ygg/fork-disposition fork)))))
          (reset! released? true)
          (if reject?
            ((:error @callbacks) failure)
            ((:ok @callbacks) nil))
          (is (= 1 (count @outcome)))
          (if reject?
            (do
              (is (= :error (ffirst @outcome)))
              (is (identical? failure (second (first @outcome))))
              (is (= :incomplete (:status (ygg/fork-disposition fork))))
              (is (= :mutating (:phase (ygg/fork-disposition fork))))
              (is (not (ygg/open-fork? fork)) "A failed mutation cannot reopen ownership")
              (is (thrown? clojure.lang.ExceptionInfo
                           (ygg/discard-fork! fork {:sync? true}))))
            (do
              (is (= :ok (ffirst @outcome)))
              (is (= (case operation :discard :discarded :merge :merged)
                     (:status (ygg/fork-disposition fork))))
              (settle! fork {:sync? true :force true})
              (is (= 1 @calls) "An acknowledged settlement is idempotent")))))
      (finally
        ;; No threads, tasks or native resources exist in this fixture. Keep
        ;; callbacks alive until the held native operation has actually replied.
        (when (and @callbacks (not @released?))
          (binding [ec/*execution-context* root
                    pcps/*in-trampoline* false]
            ((:error @callbacks) failure)))
        ;; Rejection deliberately retains incomplete semantic ownership; raw
        ;; isolated-engine termination is not an invented successful discard.
        (when-let [fork @fork*]
          (context/stop-context! (:child-ctx fork)))
        (context/close-context! root)))))

(deftest historical-discard-waits-for-native-ack
  (disposal-case! :discard false))

(deftest historical-discard-rejection-retains-incomplete-ownership
  (disposal-case! :discard true))

(deftest historical-merge-waits-for-native-overlay-cleanup
  (disposal-case! :merge false))
