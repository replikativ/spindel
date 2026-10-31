(ns org.replikativ.spindel.engine.native-custody-completion-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(deftest public-await-detaches-cancelled-observers-without-cancelling-disposal
  (let [rt (owned/runtime {:audit? true :cps-exit? true})
        root (lifetime/root-scope rt)
        {child :context bearer :capability}
        (rtp/fork-owned-world! rt {:world-id [:w 1] :owner root})
        callback (atom nil) trace (atom []) values (atom []) errors (atom [])
        cancelled-values (atom []) cancelled-errors (atom [])
        reason (ex-info "cancel observer" {})
        cleanup (owned/cspin child :cleanup
                             (try
                               (owned/park (owned/ticket :body))
                               (finally
                                 (owned/await-finalization (fn [resolve _] (reset! callback resolve))))))]
    (owned/observe! child cleanup (fn [_]) (fn [_]))
    (let [completion (rtp/discard-owned-world! rt bearer root {:operation-id :discard})]
      (is (satisfies? rtp/PCompletion completion))
      (is (not (satisfies? rtp/PWorldRelease completion)))
      (is (ifn? @callback))
      (binding [ec/*execution-context* rt]
        (let [cancelled (spin (await completion) (swap! trace conj :cancelled-resumed))
              survivor (spin (let [value (await completion)]
                               (swap! trace conj :joined)
                               value))]
          (cancelled #(swap! cancelled-values conj %) #(swap! cancelled-errors conj %))
          (survivor #(swap! values conj %) #(swap! errors conj %))
          (is (empty? @trace))
          (rtp/cancel-computation! rt cancelled (spin-core/spin-id cancelled) (spin-core/spin-body cancelled) reason)
          (is (= [reason] @cancelled-errors))
          (is (empty? @cancelled-values))
          (is (= :sealed (:status (owned/snapshot child))))
          (is (empty? @values))
          (@callback :finished)
          (is (= [nil] @values))
          (is (= [:joined] @trace))
          (is (empty? @errors))
          (is (= :released (:status (owned/snapshot child))))
          (@callback :duplicate)
          (is (= [nil] @values))
          (is (= [:joined] @trace))
          (is (= [reason] @cancelled-errors))
          (is (empty? @cancelled-values)))))
    (verify-boundaries! rt)))
