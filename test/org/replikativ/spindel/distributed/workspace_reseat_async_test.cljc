(ns org.replikativ.spindel.distributed.workspace-reseat-async-test
  "The workspace re-seat is async-correct for `:sync? false` peers — the regime of
   async storage on cljs. `resolve-system-fn` may return a core.async CHANNEL
   (konserve / datahike-cljs) or a partial-cps CPS (a yggdrasil convergent op under
   `:sync? false`); the per-peer SERIAL reseat loop normalizes either via `cps/->chan`
   and seats the RESOLVED value. RED before the async reseat (the old synchronous
   reseat seated the unresolved channel/CPS itself). Runs on JVM + cljs(node)."
  (:require #?(:clj  [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            #?(:clj  [clojure.core.async :refer [go <! timeout]]
               :cljs [cljs.core.async :refer [<! timeout] :refer-macros [go]])
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.distributed.workspace-peer :as wp]
            [org.replikativ.spindel.test-helpers :refer [async]]))

(deftest reseat-async-channel-resolve
  ;; resolve-system-fn returns a core.async channel that delivers after a delay —
  ;; the reseat loop awaits it (per system) before composing + seating.
  (async done
         (let [c    (ctx/create-execution-context)
               pref (volatile! nil)
               peer (wp/make-workspace-peer
                     {:ctx c :sync? false
                      :resolve-system-fn (fn [sid branch]
                                           (go (<! (timeout 10)) {:sid sid :branch branch}))
                      :on-reseat (fn [ws _desc]
                                   (is (= {"kb"   {:sid "kb" :branch :main}
                                           "msgs" {:sid "msgs" :branch :main}} ws)
                                       "async channel resolve seats BOTH resolved systems")
                                   (is (= ws (wp/current-workspace @pref))
                                       "current-workspace reflects the async seat")
                                   (wp/stop-peer! @pref)
                                   (ctx/stop-context! c)
                                   (done))})]
           (vreset! pref peer)
           (wp/set-descriptor! peer {:branch  :main
                                     :systems {"kb"   {:branch :main :head "h1"}
                                               "msgs" {:branch :main :head "h2"}}})
           (wp/apply-head-update! peer "kb" :main "h1")
           (wp/apply-head-update! peer "msgs" :main "h2"))))

(deftest reseat-async-cps-resolve
  ;; resolve-system-fn returns a partial-cps CPS `(fn [resolve reject])` — exactly the
  ;; shape a yggdrasil convergent op returns under `:sync? false`. cps/->chan invokes
  ;; it directly (no trampoline rebind needed) and the loop seats the resolved value.
  (async done
         (let [c    (ctx/create-execution-context)
               pref (volatile! nil)
               peer (wp/make-workspace-peer
                     {:ctx c :sync? false
                      :resolve-system-fn (fn [sid _branch]
                                           (fn [resolve _reject] (resolve {:cps sid})))
                      :on-reseat (fn [ws _desc]
                                   (is (= {"kb" {:cps "kb"}} ws)
                                       "partial-cps CPS resolve seats the resolved value")
                                   (wp/stop-peer! @pref)
                                   (ctx/stop-context! c)
                                   (done))})]
           (vreset! pref peer)
           (wp/set-descriptor! peer {:branch :main :systems {"kb" {:branch :main :head "h1"}}})
           (wp/apply-head-update! peer "kb" :main "h1"))))

#?(:clj
   (deftest reseat-async-error-aborts
     ;; a rejecting/erroring resolve must NOT seat garbage — it aborts, records the
     ;; error, and leaves the workspace unseated (the next nudge retries).
     (let [c    (ctx/create-execution-context)
           peer (wp/make-workspace-peer
                 {:ctx c :sync? false
                  :resolve-system-fn (fn [_ _] (go (ex-info "resolve-boom" {})))})]
       (try
         (wp/set-descriptor! peer {:branch :main :systems {"kb" {:branch :main :head "h1"}}})
         (wp/apply-head-update! peer "kb" :main "h1")
         (loop [n 0]
           (when (and (nil? (:last-reseat-error @peer)) (< n 150))
             (Thread/sleep 20) (recur (inc n))))
         (is (nil? (wp/current-workspace peer)) "errored resolve did NOT seat")
         (is (some? (:last-reseat-error @peer)) "the resolve error was recorded")
         (finally (wp/stop-peer! peer) (ctx/stop-context! c))))))
