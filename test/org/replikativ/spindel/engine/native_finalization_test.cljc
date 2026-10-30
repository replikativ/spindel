(ns org.replikativ.spindel.engine.native-finalization-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]))

(defn runtime [] (c/runtime {:cps-exit? true :audit? true}))
(defn empty-cleanup? [rt]
  (let [state (c/snapshot rt)] (and (empty? (:native state)) (empty? (:cleanup-cells state)))))

(deftest cancelled-body-retains-state-until-async-finally-physically-returns
  (let [rt (runtime) gate (c/ticket :body) callback (atom nil) trace (atom []) outcomes (atom [])
        s (c/cspin rt :spin
                   (let [cell (c/signal rt :cell 41)]
                     (try (c/park gate)
                          (finally
                            (swap! trace conj [:before (c/read-signal rt cell)])
                            (c/await-finalization (fn [r _] (reset! callback r)))
                            (c/set-signal! rt cell 42)
                            (swap! trace conj [:after (c/read-signal rt cell)
                                               (c/join-ready? rt [:spin 1])])))))]
    (c/observe! rt s #(swap! outcomes conj [:ok %]) #(swap! outcomes conj [:error %]))
    (let [old-body-callback (c/pending-ticket rt gate)]
      (c/cancel-spin! rt s)
      (is (= [[:before 41]] @trace))
      (is (= [:error] (mapv first @outcomes)))
      (is (false? (c/join-ready? rt [:spin 1])))
      (is (nil? (get-in (c/snapshot rt) [:entities :cell])))
      (is (zero? (:retired-ordinary-references (c/storage-stats rt))))
      (c/cancel-spin! rt s)
      (c/resume-ticket! rt old-body-callback :late-body)
      (is (= [[:before 41]] @trace))
      (@callback :cleaned)
      (is (= [[:before 41] [:after 42 false]] @trace))
      (is (c/join-ready? rt [:spin 1]))
      (is (empty-cleanup? rt))
      (@callback :duplicate)
      (is (= [[:before 41] [:after 42 false]] @trace)))
    (verify-boundaries! rt)))

(deftest cancellation-preserves-a-finalizer-already-waiting-on-success
  (let [rt (runtime) callback (atom nil) trace (atom []) outcomes (atom [])
        s (c/cspin rt :spin
                   (let [cell (c/signal rt :cell 10)]
                     (try :success
                          (finally
                            (c/await-finalization (fn [r _] (reset! callback r)))
                            (c/swap-signal! rt cell inc)
                            (swap! trace conj (c/read-signal rt cell))))))]
    (c/observe! rt s #(swap! outcomes conj [:ok %]) #(swap! outcomes conj [:error %]))
    (is (= :cps-finalization (:kind (first (vals (:native (c/snapshot rt)))))))
    (c/cancel-spin! rt s)
    (c/cancel-spin! rt s)
    (@callback false)
    (is (= [11] @trace))
    (is (= [:error] (mapv first @outcomes)))
    (is (empty-cleanup? rt))
    (verify-boundaries! rt)))

(deftest live-finalization-can-resume-inline-or-after-physical-return
  (doseq [inline? [false true]]
    (let [rt (runtime) callback (atom nil) trace (atom [])
          s (c/cspin rt :spin
                     (try :success
                          (finally
                            (c/await-finalization (fn [r _]
                                                    (reset! callback r)
                                                    (when inline? (r nil))))
                            (swap! trace conj :finally))))]
      (c/observe! rt s #(swap! trace conj %) #(throw %))
      (when-not inline? (is (empty? @trace)) (@callback nil))
      (is (= [:finally :success] @trace))
      (is (empty-cleanup? rt))
      (@callback :duplicate)
      (is (= [:finally :success] @trace))
      (verify-boundaries! rt))))

(deftest ready-finalizer-adopts-its-exact-frame-if-cancelled-before-producer-return
  (let [rt (runtime) handle (atom nil) trace (atom [])
        s (c/cspin rt :spin
                   (try :success
                        (finally
                          (c/await-finalization (fn [r _]
                                                  (r :ready)
                                                  (c/cancel-spin! rt @handle)
                                                  (swap! trace conj :producer-return)))
                          (swap! trace conj [:finally (c/join-ready? rt [:spin 1])]))))]
    (reset! handle s)
    (c/observe! rt s #(swap! trace conj [:ok %]) (fn [_] (swap! trace conj :cancelled)))
    (is (= [:producer-return [:finally false] :cancelled] @trace))
    (is (empty-cleanup? rt))
    (verify-boundaries! rt)))

(deftest cooperative-running-cancellation-is-not-reported-as-cleanup-failure
  (let [rt (runtime) handle (atom nil) source (c/signal rt :input 0) trace (atom [])
        s (c/cspin rt :spin
                   (try
                     (c/cancel-spin! rt @handle)
                     (c/track source)
                     (finally
                       (c/await-finalization (fn [r _] (r :ready)))
                       (swap! trace conj :finally))))]
    (reset! handle s)
    (c/observe! rt s #(swap! trace conj [:ok %]) (fn [_] (swap! trace conj :cancelled)))
    (is (= [:finally :cancelled] @trace))
    (is (empty-cleanup? rt))
    (verify-boundaries! rt)))

(deftest stale-protected-callbacks-cannot-wake-the-next-suspension
  (let [rt (runtime) gate (c/ticket :body) callbacks (atom []) trace (atom [])
        start (fn [r _] (swap! callbacks conj r))
        s (c/cspin rt :spin
                   (try (c/park gate)
                        (finally
                          (c/await-finalization start)
                          (swap! trace conj :first)
                          (c/await-finalization start)
                          (swap! trace conj :second))))]
    (c/observe! rt s (fn [_]) (fn [_]))
    (c/cancel-spin! rt s)
    ((first @callbacks) nil)
    (is (= [:first] @trace))
    ((first @callbacks) :duplicate)
    (is (= [:first] @trace))
    ((second @callbacks) false)
    (is (= [:first :second] @trace))
    (is (empty-cleanup? rt))
    (verify-boundaries! rt)))

(deftest overlapping-parent-child-retirement-shares-retained-payloads
  (doseq [child-first? [false true]]
    (let [rt (runtime) gate (c/ticket :child-body) child-handle (atom nil)
          callbacks (atom {}) trace (atom [])
          parent (c/cspin rt :parent
                          (let [cell (c/signal rt :cell 40)
                                child (c/cspin rt :child
                                               (try (c/park gate)
                                                    (finally
                                                      (c/await-finalization (fn [r _] (swap! callbacks assoc :child r)))
                                                      (c/swap-signal! rt cell inc)
                                                      (swap! trace conj [:child (c/read-signal rt cell)]))))]
                            (reset! child-handle child)
                            (try (c/await child)
                                 (finally
                                   (c/await-finalization (fn [r _] (swap! callbacks assoc :parent r)))
                                   (c/swap-signal! rt cell inc)
                                   (swap! trace conj [:parent (c/read-signal rt cell)])))))]
      (c/observe! rt parent (fn [_]) (fn [_]))
      (when child-first? (c/cancel-spin! rt @child-handle))
      (c/cancel-spin! rt parent)
      (is (= #{:parent :child} (set (keys @callbacks))))
      (is (= 1 (count (:cleanup-cells (c/snapshot rt)))))
      (is (zero? (:retired-ordinary-references (c/storage-stats rt))))
      ((:child @callbacks) :done)
      (is (= [[:child 41]] @trace))
      (is (= 1 (count (:cleanup-cells (c/snapshot rt)))))
      ((:parent @callbacks) :done)
      (is (= [[:child 41] [:parent 42]] @trace))
      (is (empty-cleanup? rt))
      (verify-boundaries! rt))))

(deftest cleanup-source-capabilities-do-not-alias-reused-entity-ids
  (let [rt (runtime) gate (c/ticket :body) callback (atom nil) trace (atom [])
        s (c/cspin rt :spin
                   (let [old (c/signal rt :cell :original)]
                     (try (c/park gate)
                          (finally
                            (c/await-finalization (fn [r _] (reset! callback r)))
                            (c/set-signal! rt old :cleaned)
                            (swap! trace conj (c/read-signal rt old))))))]
    (c/observe! rt s (fn [_]) (fn [_]))
    (c/cancel-spin! rt s)
    (let [replacement (c/signal rt :cell :replacement)]
      (@callback :ready)
      (is (= [:cleaned] @trace))
      (is (= :replacement (c/read-signal rt replacement))))
    (is (empty-cleanup? rt))
    (verify-boundaries! rt)))

(deftest retired-terminal-outcomes-preserve-nullable-errors-without-changing-cancellation
  (doseq [payload [nil false :cleanup-error]]
    (let [results (atom [])
          rt (c/runtime {:cps-exit? true :audit? true :on-finalization-result #(swap! results conj %)})
          gate (c/ticket :body) callback (atom nil) observed (atom [])
          s (c/cspin rt :spin
                     (try (c/park gate)
                          (finally (c/await-finalization (fn [_ reject] (reset! callback reject))))))]
      (c/observe! rt s #(swap! observed conj [:ok %]) #(swap! observed conj [:error %]))
      (c/cancel-spin! rt s)
      (@callback payload)
      (is (= [:error] (mapv first @observed)))
      (is (= [{:owner [c/w [:spin 1]] :failed? true :value payload}] @results))
      (is (empty-cleanup? rt))
      (verify-boundaries! rt))))

(deftest retired-cleanup-cannot-mutate-or-observe-ordinary-engine-state
  (let [rt (runtime) gate (c/ticket :body) trace (atom [])
        other-source (c/signal rt :other-source 0)
        other (c/cspin rt :other (c/track other-source) :observed)
        stop (c/observe! rt other (fn [_]) (fn [_]))
        s (c/cspin rt :spin
                   (try (c/park gate)
                        (finally
                          (doseq [effect [(fn [] (c/cancel-spin! rt other))
                                          stop
                                          (fn [] (c/release-idle! rt))
                                          (fn [] (c/notify-unreachable! rt other))
                                          (fn [] (c/signal rt :new 0))
                                          (fn [] (c/cspin rt :new-spin :value))
                                          (fn [] (c/observe! rt other identity identity))
                                          (fn [] (c/read-signal rt other-source))
                                          (fn [] (c/set-signal! rt other-source 1))
                                          (fn [] (c/read-application-state rt [:app :cell]))
                                          (fn [] (c/swap-application-state! rt [:app :cell] inc nil))]]
                            (let [before (c/snapshot rt)
                                  refused? (try (effect) false (catch #?(:clj Throwable :cljs :default) _ true))]
                              (is refused?)
                              (is (= before (c/snapshot rt)))))
                          (swap! trace conj :finally))))]
    (c/observe! rt s (fn [_]) (fn [_]))
    (c/cancel-spin! rt s)
    (is (= [:finally] @trace))
    (is (empty-cleanup? rt))
    (stop)
    (verify-boundaries! rt)))

(deftest terminal-result-observers-run-after-physical-return-and-drain-fully
  (let [results (atom []) callback (atom nil) failure (ex-info "observer" {})
        target (atom nil)
        rt (c/runtime {:cps-exit? true :audit? true
                       :on-finalization-result (fn [result]
                                                 (swap! results conj [result (c/join-ready? @target [:spin 1])])
                                                 (throw failure))})
        gate (c/ticket :body)
        s (c/cspin rt :spin
                   (try (c/park gate)
                        (finally (c/await-finalization (fn [r _] (reset! callback r))))))]
    (reset! target rt)
    (c/observe! rt s (fn [_]) (fn [_]))
    (c/cancel-spin! rt s)
    (is (identical? failure (try (@callback :done) nil (catch #?(:clj Throwable :cljs :default) e e))))
    (is (= [true] (mapv second @results)))
    (is (= [true] (mapv #(get-in % [0 :failed?]) @results)))
    (is (empty-cleanup? rt))
    (verify-boundaries! rt)))

#?(:clj
   (deftest cross-thread-delivery-and-cancellation-cannot-claim-a-second-frame
     (doseq [deliver-first? [false true] iteration (range 10)]
       (let [rt (runtime) entered (promise) release (promise) callback (atom nil)
             trace (atom []) observer (atom [])
             s (c/cspin rt :spin
                        (try :success
                             (finally
                               (c/await-finalization
                                (fn [r _]
                                  (reset! callback r) (deliver entered true)
                                  (deref release 5000 nil)
                                  (swap! trace conj :producer-return)))
                               (swap! trace conj :finally))))
             driver (future (c/observe! rt s #(swap! observer conj [:ok %]) #(swap! observer conj [:error %])))]
         (try
           (is (= true (deref entered 5000 :timeout)))
           (let [settle (fn []
                          (let [delivered (future (@callback :ready))]
                            (is (not= :timeout (deref delivered 5000 :timeout)))))]
             (if deliver-first?
               (do (settle) (c/cancel-spin! rt s))
               (do (c/cancel-spin! rt s) (settle))))
           (is (empty? @trace) "callback must not execute another slice before producer return")
           (is (false? (c/join-ready? rt [:spin 1])))
           (deliver release true)
           (is (not= :timeout (deref driver 5000 :timeout)))
           (is (= [:producer-return :finally] @trace))
           (is (= [:error] (mapv first @observer)))
           (is (empty-cleanup? rt))
           (verify-boundaries! rt)
           (finally (deliver release true) (deref driver 5000 nil)))))))

(deftest stale-callback-cannot-target-a-recycled-run-slot
  (let [rt (runtime) gate (c/ticket :body) callbacks (atom []) trace (atom [])
        s (c/cspin rt :spin
                   (try (c/park gate)
                        (finally
                          (c/await-finalization (fn [r _] (swap! callbacks conj r)))
                          (swap! trace conj :finally))))]
    (c/observe! rt s (fn [_]) (fn [_]))
    (c/cancel-spin! rt s)
    ((first @callbacks) :first)
    (is (pos? (:pooled-runs (c/storage-stats rt))))
    (c/observe! rt s (fn [_]) (fn [_]))
    (is (zero? (:pooled-runs (c/storage-stats rt))))
    (c/cancel-spin! rt s)
    ((first @callbacks) :old-generation)
    (is (= [:finally] @trace))
    (is (false? (c/join-ready? rt [:spin 2])))
    ((second @callbacks) :second)
    (is (= [:finally :finally] @trace))
    (is (empty-cleanup? rt))
    (verify-boundaries! rt)))

(deftest profile-disabled-retains-existing-unwinding-disposer-and-cell-read-behavior
  (let [rt (c/runtime) gate (c/ticket :other) trace (atom []) handle (atom nil)
        other (c/cspin rt :other (c/park gate))
        stop (c/observe! rt other (fn [_]) (fn [_]))
        s (c/cspin rt :spin
                   (try (c/cancel-spin! rt @handle)
                        (finally
                          (swap! trace conj (c/read-application-state rt [:app :cell]))
                          (c/cancel-spin! rt other)
                          (stop)
                          (c/release-idle! rt)
                          (swap! trace conj :finally))))]
    (c/swap-application-state! rt [:app :cell] (constantly 42) nil)
    (reset! handle s)
    (c/observe! rt s (fn [_]) (fn [_]))
    (is (= [42 :finally] @trace))))

(deftest repeated-retirement-releases-private-storage-without-audit-history
  (let [rt (c/runtime {:cps-exit? true :audit? true :record-audit? false})
        gate (c/ticket :body)]
    (dotimes [i 100]
      (let [park? (atom true)
            s (c/cspin rt :spin
                       (let [cell (c/signal rt :cell i)]
                         (try (if @park? (c/park gate) :done)
                              (finally
                                (c/await-finalization (fn [r _] (r :ready)))
                                (c/set-signal! rt cell :cleaned)))))]
        (c/observe! rt s (fn [_]) (fn [_]))
        (c/cancel-spin! rt s)
        ;; The root still owns an unfinished prototype computation after T11.
        ;; A fresh completed generation releases that ordinary ownership too.
        (reset! park? false)
        (c/observe! rt s (fn [_]) (fn [_]))
        (c/notify-unreachable! rt s)))
    (let [stats (c/storage-stats rt)]
      (is (empty? (:entities (c/snapshot rt))))
      (doseq [key [:live-runs :protected-tickets :retained-cleanup-cells :source-allocation-identities
                   :retired-ordinary-references :pooled-references :orphan-creation-links
                   :scratch-references :stale-queue-references]]
        (is (zero? (get stats key)) (pr-str [key stats]))))))

(deftest reactive-successors-preserve-the-protected-profile
  (let [rt (runtime) input (c/signal rt :input 0) callbacks (atom []) values (atom [])
        s (c/cspin rt :spin
                   (try (c/track input) :value
                        (finally (c/await-finalization (fn [r _] (swap! callbacks conj r) (r :ready))))))]
    (c/observe! rt s #(swap! values conj %) #(throw %))
    (c/set-signal! rt input 1)
    (c/set-signal! rt input 2)
    (is (= [:value :value :value] @values))
    ((first @callbacks) :old-generation)
    (is (= [:value :value :value] @values))
    (is (empty-cleanup? rt))
    (verify-boundaries! rt)))

(deftest stale-finalizers-cannot-access-a-source-adopted-by-successors
  (let [rt (runtime) input (c/signal rt :input 0) gate (c/ticket :body)
        callbacks (atom []) trace (atom [])
        s (c/cspin rt :spin
                   (let [owned (c/signal rt :owned 41)]
                     (try
                       (c/track input)
                       (c/park gate)
                       (finally
                         (c/await-finalization (fn [r _] (swap! callbacks conj r)))
                         (swap! trace conj
                                (try (c/read-signal rt owned)
                                     (catch #?(:clj Throwable :cljs :default) _ :missing)))))))]
    (c/observe! rt s (fn [_]) (fn [_]))
    (c/set-signal! rt input 1)
    (c/set-signal! rt input 2)
    (c/cancel-spin! rt s)
    (is (= 3 (count @callbacks)))
    (is (= 1 (count (:cleanup-cells (c/snapshot rt)))))
    (doseq [resume @callbacks] (resume :ready))
    (is (= {:missing 2 41 1} (frequencies @trace)))
    (is (empty-cleanup? rt))
    (is (zero? (:retired-ordinary-references (c/storage-stats rt))))
    (verify-boundaries! rt)))
