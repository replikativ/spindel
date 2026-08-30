(ns org.replikativ.spindel.ygg-bridge-portable-test
  "Cross-platform guard for the spindel↔yggdrasil bridge: register / resolve /
   enumerate / unregister must work on BOTH the JVM and cljs/node (the bridge was
   JVM-stubbed before — every fn threw \"not yet supported in ClojureScript\").

   Uses a trivial SystemIdentity system so the test exercises the bridge's
   ygg-signal plumbing without dragging in async durable storage; the durable
   fork/merge path is covered separately."
  (:require [clojure.test :refer [is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.test-helpers :as th]
            [org.replikativ.spindel.test-async :refer [deftest-async <? sync?]]
            [yggdrasil.protocols :as yp])
  #?(:cljs (:require-macros [org.replikativ.spindel.test-helpers]
                            [org.replikativ.spindel.test-async :refer [deftest-async <?]])))

(defrecord TinySys [id]
  yp/SystemIdentity
  (system-id [_] id)
  (system-type [_] :tiny)
  (capabilities [_] nil))

(deftest-async register-resolve-unregister
  (th/with-ctx [ctx]
    (let [s    (->TinySys "kb")
          yref (ygg/register! s)]
      (testing "resolve by domain id and via the YggRef (both work on cljs now)"
        (is (= s (ygg/system "kb")))
        (is (= s @yref))
        (is (= "kb" (ygg/ygg-ref-id yref))))
      (testing "enumerate registered systems"
        (is (= {"kb" s} (ygg/registered-systems))))
      (testing "fork! works on cljs (was a hard throw before) — TinySys is not
                Snapshotable, so it identity-forks; the fork plumbing still runs.
                fork! is now async on cljs (`<?`); it reads the context in its sync
                prefix, so the surrounding with-ctx binding suffices at the call."
        (let [fork (<? (ygg/fork!))]
          (is (ygg/fork-handle? fork))
          (is (some? (:child-ctx fork)))
          (is (some? (:fork-id fork)))
          (is (= :shared (get-in (ygg/fork-descriptor fork)
                                 [:fork/systems "kb" :kind]))
              "the descriptor does not claim an identity-forked system is isolated")
          (<? (ygg/discard-fork! fork))))
      ;; post-await: the with-ctx binding has exited across the fork! await (partial-cps
      ;; hands a thunk to its trampoline, so `binding` does not convey), so RE-BIND the
      ;; context for these context-reading ops.
      (testing "unregister removes it"
        (binding [ec/*execution-context* ctx]
          (is (true? (ygg/unregister! "kb")))
          (is (nil? (ygg/system "kb")))
          (is (= {} (ygg/registered-systems))))))))

(deftest-async settlement-cps-is-lazy-single-execution-and-replayable
  (th/with-ctx [ctx]
    (let [fork (<? (ygg/fork! {:systems :none :sync? sync?}))
          callbacks (atom 0)
          settlement (ygg/discard-fork! fork {:sync? sync?
                                              :on-discard (fn [_] (swap! callbacks inc))})]
      #?(:cljs
         (is (ygg/open-fork? fork)
             "constructing the CPS expression does not consume settlement authority"))
      (is (nil? (<? settlement)))
      (is (nil? (<? settlement))
          "invoking the same CPS expression again replays its result")
      (is (= 1 @callbacks)
          "the settlement body and callback execute exactly once")
      (is (nil? (<? (ygg/discard-fork! fork {:sync? sync?})))
          "a later idempotent call preserves the asynchronous return shape")
      (is (= :discarded (:status (ygg/fork-disposition fork)))))))

(deftest-async settlement-authority-partition-is-portable
  (th/with-ctx [ctx]
    (ygg/register! (->TinySys "kb"))
    (ygg/register! (->TinySys "ledger"))
    (ygg/register! (->TinySys "files"))
    (let [whole (<? (ygg/fork! {:sync? sync? :owner :run}))
          [knowledge files]
          (ygg/partition-fork!
           whole
           [{:systems #{"kb" "ledger"} :owner :knowledge-review}
            {:systems #{"files"} :owner :code-review}])
          [kb ledger]
          (ygg/partition-fork!
           knowledge
           [{:systems #{"kb"} :owner :research-review}
            {:systems #{"ledger"} :owner :accounting-review}])]
      (is (= :partitioned (:status (ygg/fork-disposition whole))))
      (is (not (ygg/open-fork? whole)))
      (is (= :partitioned (:status (ygg/fork-disposition knowledge)))
          "a partition can be recursively subdivided without a new world fork")
      (is (= #{"kb"} (set (keys (:fork/systems (ygg/fork-descriptor kb))))))
      (is (= #{"ledger"} (set (keys (:fork/systems (ygg/fork-descriptor ledger))))))
      (is (not= (:fork/settlement-id (ygg/fork-descriptor kb))
                (:fork/settlement-id (ygg/fork-descriptor ledger))))
      (binding [ec/*execution-context* (:child-ctx whole)]
        (let [register-error (try
                               (ygg/register! (->TinySys "late"))
                               nil
                               (catch #?(:clj Throwable :cljs :default) error error))
              unregister-error (try
                                 (ygg/unregister! "kb")
                                 nil
                                 (catch #?(:clj Throwable :cljs :default) error error))]
          (is (= ::ygg/fork-world-shape-frozen
                 (:type (ex-data register-error))))
          (is (= ::ygg/fork-world-shape-frozen
                 (:type (ex-data unregister-error))))))
      (is (nil? (<? (ygg/discard-fork! kb {:sync? sync?}))))
      (is (nil? (<? (ygg/discard-fork! ledger {:sync? sync?}))))
      (is (nil? (<? (ygg/discard-fork! files {:sync? sync?})))))))
