(ns org.replikativ.spindel.distributed.workspace-peer-sync-test
  "Tests for the workspace-peer live-wiring glue (callback translation +
   attach opts). The real konserve-sync subscription / signal_sync path is
   exercised end-to-end in dvergr (where datahike + yggdrasil + konserve-sync
   coexist and the head-token choice is pinned against real stored-dbs).
   CLJ-only."
  (:require #?(:clj  [clojure.test :refer [deftest testing is]]
               :cljs [cljs.test :refer-macros [deftest testing is]])
            #?(:clj  [clojure.core.async :refer [go <! <!!]]
               :cljs [cljs.core.async :refer [<!] :refer-macros [go]])
            ;; sync is fully cljc; merge-fork-remote! is pure (mock-injected, no
            ;; execution context) so it runs — and forces compilation of the whole
            ;; workspace_peer_sync + workspace_peer source — on BOTH platforms.
            [org.replikativ.spindel.distributed.workspace-peer-sync :as sync]
            [org.replikativ.spindel.test-helpers :refer [async]]
            ;; context + the konserve-sync walker are only on the JVM :test classpath;
            ;; the tests using them stay JVM-only.
            #?@(:clj [[org.replikativ.spindel.engine.context :as ctx]
                      [org.replikativ.spindel.distributed.workspace-peer :as wp]
                      [konserve-sync.walkers.crdt :as kcrdt]])))

;; ---------------------------------------------------------------------------
;; Cross-platform (cljc): the fork-merge lifecycle counterpart, pure mocks.
;; ---------------------------------------------------------------------------

;; mock yggdrasil ops: checkout returns a {:sid :branch} system value; snapshot-id
;; is a stand-in [sid branch] token; merge! takes the fork BRANCH KEYWORD as source
;; (the real ygg/merge! contract — NOT a system).
(def ^:private mock-checkout (fn [base branch] {:sid (:sid base) :branch branch}))
(def ^:private mock-snap-id (fn [sys] [(:sid sys) (:branch sys)]))

;; merge-fork-remote! returns a CHANNEL now (async-uniform); `<!` it. Cross-platform
;; via the `async`/`done` harness (JVM blocks on a promise; cljs uses cljs.test/async).
(deftest test-merge-fork-remote-folds-fork-into-parent
  (async done
         (go
           (testing "success: each system's fork BRANCH KEYWORD merges into the parent"
             (let [fork-desc {:branch :fork-1 :owner :peer-a
                              :fork-of {:branch :main :heads {"kb" "c1" "msgs" "c2"}}
                              :systems {"kb"   {:branch :fork-1 :head "c1"}
                                        "msgs" {:branch :fork-1 :head "c2"}}}
                   merged-calls (atom [])
                   res (<! (sync/merge-fork-remote!
                            fork-desc (fn [sid] {:sid sid})
                            :checkout-fn mock-checkout :snapshot-id-fn mock-snap-id
                            :merge-fn (fn [psys src _opts]
                                        (swap! merged-calls conj [(:sid psys) (:branch psys) src])
                                        (assoc psys :merged-from src))
                            :conflicts-fn (fn [_psys _pa _fb] nil)))]
               (is (= #{["kb" :main :fork-1] ["msgs" :main :fork-1]} (set @merged-calls)))
               (is (= {:sid "kb" :branch :main :merged-from :fork-1} (get-in res [:merged "kb"])))
               (is (empty? (:conflicts res)))))
           (testing "FAIL-SAFE: a conflicting system aborts the WHOLE merge (nothing merged)"
             (let [fork-desc {:branch :fork-1 :fork-of {:branch :main :heads {"kb" "c1"}}
                              :systems {"kb" {:branch :fork-1 :head "c1"}}}
                   merge-called (atom false)
                   res (<! (sync/merge-fork-remote!
                            fork-desc (fn [sid] {:sid sid})
                            :checkout-fn mock-checkout :snapshot-id-fn mock-snap-id
                            :merge-fn (fn [& _] (reset! merge-called true) :merged)
                            :conflicts-fn (fn [_psys _pa _fb] [{:attr :title}])))]
               (is (= {} (:merged res)) "no system merged")
               (is (= {"kb" [{:attr :title}]} (:conflicts res)))
               (is (false? @merge-called) "merge-fn never called — aborted before merging")))
           (testing "a THROWING conflict detector counts as indeterminate (fail-safe abort)"
             (let [fork-desc {:branch :fork-1 :fork-of {:branch :main}
                              :systems {"kb" {:branch :fork-1 :head "c1"}}}
                   res (<! (sync/merge-fork-remote!
                            fork-desc (fn [sid] {:sid sid})
                            :checkout-fn mock-checkout :snapshot-id-fn mock-snap-id
                            :merge-fn (fn [& _] :merged)
                            :conflicts-fn (fn [_psys _pa _fb] (throw (ex-info "boom" {})))))]
               (is (empty? (:merged res)))
               (is (true? (get-in res [:conflicts "kb" 0 :indeterminate?])))))
           (testing ":force skips the conflict pre-check and merges anyway"
             (let [fork-desc {:branch :fork-1 :fork-of {:branch :main}
                              :systems {"kb" {:branch :fork-1 :head "c1"}}}
                   res (<! (sync/merge-fork-remote!
                            fork-desc (fn [sid] {:sid sid})
                            :checkout-fn mock-checkout :snapshot-id-fn mock-snap-id
                            :merge-fn (fn [psys src _] (assoc psys :forced src))
                            :conflicts-fn (fn [_psys _pa _fb] (throw (ex-info "would-conflict" {})))
                            :opts {:force true}))]
               (is (= {:sid "kb" :branch :main :forced :fork-1} (get-in res [:merged "kb"])))
               (is (empty? (:conflicts res)))))
           (done))))

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

     (deftest test-wire-topology-replays-store-subscriptions
       (testing "wire-topology! subscribes each system's store under its :topic and
                 routes head updates into the peer's gate — data-driven replay"
         (let [captured (atom {})
               fake-subscribe (fn [_cp topic store opts]
                                (swap! captured assoc topic {:store store :opts opts})
                                (keyword (str "ch-" (name topic))))
               p (peer)
               desc {:branch :main
                     :systems {"kb"   {:branch :main :head "c1" :topic :kb-topic}
                               "msgs" {:branch :main :head "c2" :topic :msgs-topic}}}
               store-lookup {"kb" :kb-store "msgs" :msgs-store}
               ret (sync/wire-topology! p :client-peer desc store-lookup
                                        :head-token-fn identity   ; the synced value IS the token
                                        :subscribe-fn fake-subscribe)]
           (testing "each system's store subscribed under its :topic with the looked-up store"
             (is (= #{:kb-topic :msgs-topic} (set (keys @captured))))
             (is (= :kb-store (get-in @captured [:kb-topic :store])))
             (is (= :msgs-store (get-in @captured [:msgs-topic :store]))))
           (testing "per-system subscribe channels returned; no :descriptor-topic ⇒ nil descriptor"
             (is (= {"kb" :ch-kb-topic "msgs" :ch-msgs-topic} (:stores ret)))
             (is (nil? (:descriptor ret))))
           (testing "the wired on-key-update advances the peer's gate as each head lands"
             (wp/set-descriptor! p desc)
             ((get-in @captured [:kb-topic :opts :on-key-update]) :main "c1" :assoc)
             (is (false? (:ready? (wp/gate-status p))) "only kb landed → still pending msgs")
             ((get-in @captured [:msgs-topic :opts :on-key-update]) :main "c2" :assoc)
             (is (true? (:ready? (wp/gate-status p))) "both heads local → gate ready")))
         (testing "a system without :topic is skipped (not every system is wire-synced)"
           (let [c2 (atom {})
                 fs (fn [_cp topic store _opts] (swap! c2 assoc topic store) :ch)]
             (sync/wire-topology! (peer) :client-peer
                                  {:systems {"kb" {:branch :main :head "c1"}}}
                                  {"kb" :kb-store} :subscribe-fn fs)
             (is (empty? @c2))))))

     (deftest test-fork-remote-creates-isolated-local-branch
       (testing "fork-remote! branches each followed system locally onto the fork
                 branch, claims the owner, and re-seats the peer onto the writable
                 fork — no remote sync (isolated single-writer)"
         (let [branched (atom [])
               p (peer)
               parent {:branch :main
                       :owner :server
                       :systems {"kb"   {:branch :main :head "c1" :topic :kb-topic}
                                 "msgs" {:branch :main :head "c2" :topic :msgs-topic}}}
               fork-desc (<!! (sync/fork-remote!
                               p parent :fork-1 :peer-a
                               (fn [sid] {:sid sid})                     ; system-lookup
                               :branch-fn (fn [sys b] (swap! branched conj [(:sid sys) b]))))]
           (testing "each system branched locally onto :fork-1"
             (is (= #{["kb" :fork-1] ["msgs" :fork-1]} (set @branched))))
           (testing "fork descriptor claimed + :fork-of anchored to parent heads"
             (is (= :fork-1 (:branch fork-desc)))
             (is (= :peer-a (:owner fork-desc)))
             (is (= {:branch :main :heads {"kb" "c1" "msgs" "c2"}} (:fork-of fork-desc))))
           (testing "peer re-seated onto the fork branch (local head immediately present)"
             (is (true? (:ready? (wp/gate-status p))))
             (is (= {"kb"   {:sid "kb" :branch :fork-1}
                     "msgs" {:sid "msgs" :branch :fork-1}}
                    (wp/current-workspace p))))
           (testing "writable only by the claimed owner, not the parent's :server"
             (is (true? (wp/peer-writable? p :peer-a)))
             (is (false? (wp/peer-writable? p :server)))))))

     (deftest test-wire-topology-dispatches-on-role
       (testing "wire-topology! routes each system by :role — :bidirectional →
                 convergent live sync (sync-fn), :subscriber (default) → one-way
                 store follow (subscribe-fn)"
         (let [synced (atom []) subbed (atom [])
               desc {:systems {"crdt" {:topic :crdt-topic :role :bidirectional :owner? true}
                               "dh"   {:topic :dh-topic :role :subscriber}}}
               ret (sync/wire-topology!
                    (peer) :client-peer desc
                    (fn [sid] (keyword (str "store-" (name sid))))
                    :subscribe-fn (fn [_cp topic _store _opts] (swap! subbed conj topic) :sub-ch)
                    :sync-fn (fn [sid topic owner?] (swap! synced conj [sid topic owner?]) :sync-ch))]
           (testing "the convergent system is wired bidirectionally, owner? from the descriptor"
             (is (= [["crdt" :crdt-topic true]] @synced))
             (is (= :sync-ch (get-in ret [:synced "crdt"]))))
           (testing "the durable system is store-followed, not δ-sync'd"
             (is (= [:dh-topic] @subbed))
             (is (= :sub-ch (get-in ret [:stores "dh"]))))
           (testing "the two paths don't cross"
             (is (nil? (get-in ret [:synced "dh"])))
             (is (nil? (get-in ret [:stores "crdt"])))))))

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
         (testing "on-roots fires (with the local store) only on a :crdt.head/<branch> cell"
           (let [oku (get-in @captured [:opts :on-key-update])]
             (oku (random-uuid) {:node :data} :assoc)     ; a block — ignored
             (is (empty? @fired))
             (oku :crdt/branches #{:main} :assoc)          ; the registry — ignored
             (is (empty? @fired))
             (oku :crdt.head/main {:adds :a :removals :r} :assoc)  ; a head cell — fires
             (is (= [:the-store] @fired))))
         (testing "crdt-sync-opts is the server-side register bundle"
           (is (= kcrdt/crdt-walk-fn (:walk-fn (kcrdt/crdt-sync-opts)))))))))
