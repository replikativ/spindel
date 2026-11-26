(ns org.replikativ.spindel.v2.dom.batch-cljs-test
  "CB2 (phase-d addendum §3.8.9): on CLJS a bare swap! on a world that is
   not inline goes through host-call!, which enqueues the item and then
   throws because it did not run synchronously. The operation is already
   queued: it applies once, and a retry would apply it twice. In a `batch`
   the nested swap! runs in the item: once, no throw."
  (:require [cljs.test :refer-macros [deftest is async]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.dom.render :refer [batch]]))

(defn- read-later
  "Calls `(k v)` with the value of `s` after the world has drained."
  [s k]
  (js/setTimeout #(v2/value-async s (fn [v _] (k v))) 20))

(deftest cb2-swap-on-a-non-inline-world
  (async done
         (let [w (v2/world {:inline? false})
               s (v2/signal w 0)
               thrown (try (swap! s inc) nil (catch :default e (ex-message e)))]
           (is (re-find #"synchronously" (str thrown)) "a bare swap! throws after enqueueing")
           (read-later s (fn [v]
                           (is (= 1 v) "it applied once")
                           (let [thrown (binding [v2/*world* w]
                                          (try (batch (swap! s inc)) nil (catch :default e e)))]
                             (is (nil? thrown) "in a batch: no throw")
                             (read-later s (fn [v]
                                             (is (= 2 v) "once")
                                             (v2/release-world! w)
                                             (done)))))))))
