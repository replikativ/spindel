(ns org.replikativ.spindel.distributed.workspace-peer-sync-test
  "Tests for the workspace-peer live-wiring glue (callback translation +
   attach opts). The real konserve-sync subscription / signal_sync path is
   exercised end-to-end in dvergr (where datahike + yggdrasil + konserve-sync
   coexist and the head-token choice is pinned against real stored-dbs).
   CLJ-only."
  #?(:clj
     (:require [clojure.test :refer [deftest testing is]]
               [org.replikativ.spindel.engine.context :as ctx]
               [org.replikativ.spindel.distributed.workspace-peer :as wp]
               [org.replikativ.spindel.distributed.workspace-peer-sync :as sync]
               [konserve-sync.walkers.yggdrasil-registry :as regw])
     :cljs
     (:require [cljs.test :refer-macros [deftest testing is]])))

#?(:clj
   (do
     (defn- peer []
       (wp/make-workspace-peer
        {:ctx (ctx/create-execution-context)
         :resolve-system-fn (fn [sid branch] {:sid sid :branch branch})}))

     (deftest test-head-update-handler-translates-branch-pointers
       (let [p (peer)
             _ (wp/set-descriptor! p {:branch :fork
                                      :systems {"kb" {:branch :fork :head "f1"}}})
             h (sync/head-update-handler p "kb" :head-token-fn (constantly "f1"))]
         (testing "the :branches set key is ignored (not a HEAD)"
           (h :branches #{:fork} :assoc)
           (is (false? (:ready? (wp/gate-status p)))))
         (testing "a non-keyword (content block) key is ignored"
           (h "block-uuid-addr" {:node :data} :assoc)
           (is (false? (:ready? (wp/gate-status p)))))
         (testing "the fork branch-pointer key drives the gate to ready + re-seats"
           (h :fork {:some :stored-db} :assoc)
           (is (true? (:ready? (wp/gate-status p))))
           (is (= {"kb" {:sid "kb" :branch :fork}} (wp/current-workspace p))))))

     (deftest test-attach-store-forwards-opts-and-wires-callback
       (let [captured (atom nil)
             fake-subscribe (fn [client-peer topic store opts]
                              (reset! captured {:cp client-peer :topic topic
                                                :store store :opts opts})
                              :fake-chan)
             p (peer)
             ret (sync/attach-store! p :client-peer "kb" :kb-topic :the-store
                                     :subscribe-fn fake-subscribe
                                     :on-complete :done-fn
                                     :head-token-fn (constantly "x"))]
         (testing "subscribe-fn is called with topic/store and the channel returned"
           (is (= :fake-chan ret))
           (is (= :kb-topic (:topic @captured)))
           (is (= :the-store (:store @captured)))
           (is (= :client-peer (:cp @captured))))
         (testing "on-key-update is wired and :on-complete forwarded"
           (is (fn? (get-in @captured [:opts :on-key-update])))
           (is (= :done-fn (get-in @captured [:opts :on-complete]))))
         (testing "the wired on-key-update actually advances the peer's gate"
           (wp/set-descriptor! p {:branch :main
                                  :systems {"kb" {:branch :main :head "x"}}})
           ((get-in @captured [:opts :on-key-update]) :main {:db :v} :assoc)
           (is (true? (:ready? (wp/gate-status p)))))))

     (deftest test-subscribe-registry-fires-on-roots
       (let [captured (atom nil)
             fired (atom [])
             fake-subscribe (fn [_cp _topic store opts]
                              (reset! captured {:store store :opts opts}) :ch)
             ret (sync/subscribe-registry! :client-peer :reg-topic :the-store
                                           :on-roots (fn [s] (swap! fired conj s))
                                           :on-complete :done
                                           :subscribe-fn fake-subscribe)]
         (is (= :ch ret))
         (is (= :the-store (:store @captured)))
         (is (= :done (get-in @captured [:opts :on-complete])))
         (testing "on-roots fires (with the local store) only on :registry/roots"
           (let [oku (get-in @captured [:opts :on-key-update])]
             (oku (random-uuid) {:node :data} :assoc)     ; a block — ignored
             (is (empty? @fired))
             (oku :registry/roots {:tsbs :addr} :assoc)   ; the pointer — fires
             (is (= [:the-store] @fired))))
         (testing "registry-sync-opts is the server-side register bundle"
           (is (= regw/registry-walk-fn (:walk-fn (regw/registry-sync-opts)))))))))
