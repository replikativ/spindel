(ns org.replikativ.spindel.distributed.signal-sync-test
  "merge-fn on SignalSyncStrategy: a convergent ygg-signal JOINS an incoming
   remote value with the local one (so concurrent local + remote updates
   converge) instead of clobbering it under blind LWW. nil merge-fn = the
   LWW-reset default."
  (:require #?(:clj  [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [clojure.set :as set]
            [kabel.pubsub.protocol :as proto]
            [org.replikativ.spindel.core :as s]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.distributed.signal-sync :as ss]))

(deftest merge-fn-joins-instead-of-resetting
  (testing "with merge-fn, an incoming remote value is JOINED with the local one"
    (let [a     (atom #{:x})
          strat (ss/->SignalSyncStrategy a nil set/union nil true nil)]
      (proto/-apply-publish strat {:value #{:y}})
      (is (= #{:x :y} @a) "convergent publish: local :x survives the remote :y")
      (proto/-apply-handshake-item strat {:value #{:z}})
      (is (= #{:x :y :z} @a) "convergent handshake adopt also joins"))))

(deftest no-merge-fn-is-lww-reset
  (testing "without merge-fn, an incoming value overwrites local (LWW — default)"
    (let [a     (atom #{:x})
          strat (ss/->SignalSyncStrategy a nil nil nil nil nil)]
      (proto/-apply-publish strat {:value #{:y}})
      (is (= #{:y} @a) "LWW: remote replaces local"))))

(deftest op-only-convergent-ignores-value-never-clobbers
  (testing "an OP-only convergent subscriber (apply-delta-fn set, merge-fn NIL) must NOT
            LWW-reset on an incoming {:value} (e.g. a connect-handshake snapshot) — that
            would clobber concurrent local state. The value is ignored; convergence rides
            the δ path. (Regression for the handshake-{:value} LWW footgun.)"
    (let [a       (atom #{:x})
          apply-δ (fn [cur d] (set/union (or cur #{}) d))
          strat   (ss/->SignalSyncStrategy a nil nil apply-δ true nil)]
      ;; pre-fix: a raw {:value} (no :delta) fell through to LWW reset → clobbered :x
      (proto/-apply-handshake-item strat {:value #{:y}})
      (is (= #{:x} @a) "value IGNORED — local :x survives (footgun closed)")
      (proto/-apply-publish strat {:value #{:w}})
      (is (= #{:x} @a) "a live {:value} is ignored too — only the δ path mutates")
      (proto/-apply-publish strat {:delta #{:z}})
      (is (= #{:x :z} @a) "the δ/OP path still applies normally"))))

(deftest async-merge-joins-after-suspension
  (testing "with merge-fn + :sync? false (a CPS-returning join, as a durable :sync? false
            ygg-signal yields), the incoming value is committed only once the join
            resolves — proving the convergent join can SUSPEND on IO before commit"
    (let [a          (atom #{:x})
          ;; A deferred CPS join: captures `resolve` so the test can fire it
          ;; later, modelling a konserve-backed `c/-join` that suspends on IO.
          fire       (atom nil)
          await-join (fn [cur incoming]
                       (fn [resolve _reject]
                         (reset! fire #(resolve (set/union (or cur #{}) incoming)))))
          ;; ONE merge-fn, :sync? false (the default — async) → signal-sync awaits
          ;; the CPS before commit
          strat      (ss/->SignalSyncStrategy a nil await-join nil false nil)]
      (proto/-apply-publish strat {:value #{:y}})
      (is (= #{:x} @a) "not yet joined — the async join is suspended awaiting IO")
      (@fire)
      (is (= #{:x :y} @a) "joined after the async resolve fires (local :x survives)"))))

(deftest signalref-convergent-receive-commits
  (testing "apply-incoming! on a SignalRef (sync? true, deltaable value) commits via
            cas-read/cas! — was a HANG (cas! compared @ unwrapped vs the raw node value)
            or a THROW (swap-vals! needs IAtom2; SignalRef is IAtom). Plain-atom callers
            were unaffected, which is why it stayed latent."
    (let [c (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* c]
          (let [sg    (s/signal #{:x})
                _     @sg                                   ; force node init
                strat (ss/->SignalSyncStrategy sg nil set/union nil true nil)]
            (proto/-apply-publish strat {:value #{:y}})
            (is (= #{:x :y} @sg) "SignalRef convergent receive joins; local :x survives")
            (proto/-apply-handshake-item strat {:value #{:z}})
            (is (= #{:x :y :z} @sg) "handshake adopt joins too")))
        (finally (ctx/stop-context! c))))))
