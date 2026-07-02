(ns org.replikativ.spindel.ygg-bridge-portable-test
  "Cross-platform guard for the spindel↔yggdrasil bridge: register / resolve /
   enumerate / unregister must work on BOTH the JVM and cljs/node (the bridge was
   JVM-stubbed before — every fn threw \"not yet supported in ClojureScript\").

   Uses a trivial SystemIdentity system so the test exercises the bridge's
   ygg-signal plumbing without dragging in async durable storage; the durable
   fork/merge path is covered separately."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [org.replikativ.spindel.test-helpers :as th]
            [yggdrasil.protocols :as yp]))

(defrecord TinySys [id]
  yp/SystemIdentity
  (system-id [_] id)
  (system-type [_] :tiny)
  (capabilities [_] nil))

(deftest register-resolve-unregister
  (th/with-ctx [_ctx]
    (let [s    (->TinySys "kb")
          yref (ygg/register! s)]
      (testing "resolve by domain id and via the YggRef (both work on cljs now)"
        (is (= s (ygg/system "kb")))
        (is (= s @yref))
        (is (= "kb" (ygg/ygg-ref-id yref))))
      (testing "enumerate registered systems"
        (is (= {"kb" s} (ygg/registered-systems))))
      (testing "fork! works on cljs (was a hard throw before) — TinySys is not
                Snapshotable, so it identity-forks; the fork plumbing still runs"
        (let [fork (ygg/fork!)]
          (is (ygg/fork-handle? fork))
          (is (some? (:child-ctx fork)))
          (is (some? (:fork-id fork)))))
      (testing "unregister removes it"
        (is (true? (ygg/unregister! "kb")))
        (is (nil? (ygg/system "kb")))
        (is (= {} (ygg/registered-systems)))))))
