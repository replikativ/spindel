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
            [org.replikativ.spindel.test-async :refer [deftest-async <?]]
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
          (is (some? (:fork-id fork)))))
      ;; post-await: the with-ctx binding has exited across the fork! await (partial-cps
      ;; hands a thunk to its trampoline, so `binding` does not convey), so RE-BIND the
      ;; context for these context-reading ops.
      (testing "unregister removes it"
        (binding [ec/*execution-context* ctx]
          (is (true? (ygg/unregister! "kb")))
          (is (nil? (ygg/system "kb")))
          (is (= {} (ygg/registered-systems))))))))
