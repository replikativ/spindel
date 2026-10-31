(ns org.replikativ.spindel.lifetime.composed-release-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [clojure.walk :as walk]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.lifecycle :as lifecycle]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.engine.kernel :as kernel]))

(def a [:w 0])
(def b [:w 1])
(def c [:w 2])
(def sa [:scope :id 0])
(def sb [:scope :id 1])
(def sc [:scope :id 2])
(def kb [:cap :b])
(def kc [:cap :c])
(def moved-kb [:cap :moved-b])

(defn request [w] {:t :release-request :w w :release (lifecycle/release-id w) :reason :first-reason})
(defn phase [s w] (get-in s [:env :releases w :phase]))
(defn checked [before action]
  (let [after (m/step before action)
        edge {:before before :action action :after after}]
    (is (empty? (inv/check after)) (pr-str [action (inv/check after)]))
    (is (empty? (inv/edge-check edge)) (pr-str [action (inv/edge-check edge)]))
    after))
(defn apply-actions [s actions] (reduce checked s actions))
(defn refuses [s action error]
  (let [result (m/attempt s action)]
    (is (= error (get-in result [:refusal :error])) (pr-str result))
    (is (= s (:state result)))))
(defn normalize [s]
  (walk/postwalk (fn [value]
                   (if (and (keyword? value) (#{"cancelled" "released"} (name value))
                            (#{"org.replikativ.spindel.engine.kernel" "org.replikativ.spindel.lifetime.model"}
                             (namespace value))) (keyword "error" (name value)) value))
                 (select-keys s [:worlds :env :caps :records :custody :next-claim :serial :clocks :registry
                                 :known-worlds :lineages :generation-clock])))
(defn parity [before action after]
  ;; Settlement/dispatch is not implemented in the kernel. Restore exact
  ;; checkpoints, then compare supported actions on both independent stores.
  (doseq [cells? [false true]]
    (let [implementation (kernel/restore before {:cells? cells?})]
      (kernel/step! implementation action)
      (is (= (normalize after) (normalize (kernel/snapshot implementation))) (pr-str action)))))

(defn nested-worlds []
  (apply-actions (m/init-state {:slices? true})
                 [{:t :t12 :w a :scope sa :parent [:root a]}
                  {:t :t19 :w a :v b :k kb :scope sa :systems #{}}
                  {:t :t12 :w b :scope sb :parent [:root b]}
                  {:t :t19 :w b :v c :k kc :scope sb :systems #{}}]))
(defn dispatch [s w]
  (is (some? (:custody-dispatch (first (:queue (m/wr s w))))))
  (checked s {:t :queued :w w}))
(defn finish [s k]
  (let [op (:op (m/cap s k))]
    (apply-actions s [{:t :t27 :k k :op op :payload :empty :bases {} :steps []}
                      {:t :t29 :op op}])))

(deftest transitive-completion-survives-terminal-claim-removal-and-late-request
  (doseq [late-request? [false true]]
    (testing (str "request after first claim terminal: " late-request?)
      (let [initial (nested-worlds)
            closed (checked initial {:t :t13 :w a :scope sa})
            _ (parity initial {:t :t13 :w a :scope sa} closed)
            requested (if late-request? closed (checked closed (request a)))
            sealed-b (dispatch requested b)
            after-b (finish sealed-b kb)
            before-request after-b
            pending (if late-request? (checked after-b (request a)) after-b)
            _ (when late-request? (parity before-request (request a) pending))
            observer [(lifecycle/release-id a) 1]
            observe {:t :release-observe :w a :release (lifecycle/release-id a) :observer observer}
            observed (checked pending observe)]
        (is (= :released (:status (m/wr pending b))))
        (is (m/join-ready? pending a [:root a]))
        (is (m/join-ready? pending b [:root b]))
        (is (= :releasing (phase pending a)))
        (is (nil? (get-in pending [:env :releases b])))
        (is (= #{a b} (set (keys (get-in pending [:env :cleanup-targets])))))
        (is (not-any? #(= kb (:cap %)) (vals (get-in pending [:custody :claims]))))
        (is (= :waiting (get-in observed [:env :releases a :observers observer :state])))
        (parity pending observe observed)
        (let [done (finish (dispatch observed c) kc)
              repeated (checked done (assoc (request a) :reason :second-reason))
              notified (checked repeated {:t :release-notify :w a :release (lifecycle/release-id a)
                                          :observer observer})]
          (is (= :joined (phase done a)))
          (is (nil? (get-in done [:env :cleanup-targets])))
          (is (= :first-reason (get-in repeated [:env :releases a :reason])))
          (is (= 1 (count (filter #(= :release-delivery (:event %)) (:events notified)))))
          (is (= :released (:status (m/wr done c)))))))))

(deftest cyclic-custody-waits-for-real-local-return-without-cyclic-receipts
  (let [initial (nested-worlds)
        setup (apply-actions initial
                             [{:t :t12 :w c :scope sc :parent [:root c]}
                              {:t :t32 :k kb :successor moved-kb :op :move-to-c
                               :caller (m/execution-holder a sa)
                               :holder (m/execution-holder c sc) :acceptor (m/execution-holder c sc)}
                              {:t :t04 :w b :e :busy :scope [:root b] :mode :deref}
                              {:t :slice-enter :w b :r [:busy 1] :th :busy-b}
                              {:t :t13 :w b :scope sb}])
        after-c (finish (dispatch setup c) kc)
        pending (checked after-c (request c))
        observe {:t :release-observe :w c :release (lifecycle/release-id c)
                 :observer [(lifecycle/release-id c) 1]}
        observed (checked pending observe)]
    (is (= #{b c} (set (keys (get-in pending [:env :cleanup-targets])))))
    (is (= :releasing (phase pending c)))
    (is (m/join-ready? pending c [:root c]))
    (is (not (m/join-ready? pending b [:root b])))
    (is (nil? (get-in pending [:env :releases b])))
    (refuses observed (assoc observe :observer [(lifecycle/release-id c) 2] :caller-th :busy-b)
             ::lifecycle/release-self-join)
    (let [sealed-b (dispatch observed b)
          op (:op (m/cap sealed-b moved-kb))
          _ (refuses sealed-b {:t :t27 :k moved-kb :op op :payload :empty :bases {} :steps []} ::m/not-joined)
          returned (checked sealed-b {:t :t38 :th :busy-b})
          _ (parity sealed-b {:t :t38 :th :busy-b} returned)
          done (finish returned moved-kb)]
      (is (= :releasing (phase returned c)))
      (is (= :joined (phase done c)))
      (is (nil? (get-in done [:env :cleanup-targets])))
      (is (= :released (:status (m/wr done b))))
      (is (nil? (get-in done [:env :releases b]))))))

(deftest moved-away-target-survives-old-world-release-and-self-custody-completes
  (let [initial (apply-actions (m/init-state)
                               [{:t :t12 :w a :scope sa :parent [:root a]}
                                {:t :t19 :w a :v b :k kb :scope sa :systems #{}}
                                {:t :t12 :w b :scope sb :parent [:root b]}
                                {:t :t32 :k kb :successor moved-kb :op :self-move
                                 :caller (m/execution-holder a sa)
                                 :holder (m/execution-holder b sb) :acceptor (m/execution-holder b sb)}
                                {:t :t13 :w a :scope sa}])
        released-a (checked initial (request a))
        closed-b (checked released-a {:t :t13 :w b :scope sb})]
    (is (= :joined (phase released-a a)))
    (is (= :live (:status (m/wr released-a b))))
    (is (= :open (:disposition (m/cap released-a moved-kb))))
    (is (nil? (get-in released-a [:env :cleanup-targets])))
    (is (= b (:target-world (first (vals (get-in closed-b [:env :cleanup-targets b]))))))
    (is (not (m/release-ready? closed-b b)))
    (let [done (finish (dispatch closed-b b) moved-kb)
          observed (checked done (request b))]
      (is (= :joined (phase observed b)))
      (is (nil? (get-in observed [:env :cleanup-targets])))
      (is (= :joined (phase observed a))))))

(deftest parent-fork-notification-is-required-only-while-its-row-survives
  (let [initial (checked (m/init-state) {:t :t19 :w a :v b :k kb :scope [:root a] :systems #{}})
        sealed (checked initial {:t :t26 :k kb :op :explicit-discard :kind :discard
                                 :caller (m/execution-holder a [:root a])})
        released (finish sealed kb)]
    (is (some? (m/ent released a [:fork b])))
    (is (= b (:fork-released (first (:queue (m/wr released a))))))
    (let [done (checked released {:t :t36 :w a})]
      (is (nil? (m/ent done a [:fork b])))
      (is (empty? (:queue (m/wr done a)))))))

(deftest independent-proof-rejects-erased-causality-and-coordinated-early-completion
  (let [closed (checked (nested-worlds) {:t :t13 :w a :scope sa})
        requested (checked closed (request a))
        sealed (dispatch requested b)
        op (:op (m/cap sealed kb))
        prepared (checked sealed {:t :t27 :k kb :op op :payload :empty :bases {} :steps []})
        action {:t :t29 :op op}
        pending (checked prepared action)
        erased (update-in pending [:env :cleanup-targets] dissoc a)
        early (-> erased (assoc-in [:env :releases a :phase] :joined)
                  (assoc-in [:env :releases a :result] nil)
                  (update :events conj {:event :release-joined :world a :release (lifecycle/release-id a)}))
        omitted-child (update-in pending [:env :cleanup-targets] dissoc b)]
    (doseq [corrupt [erased early omitted-child]]
      (is (seq (inv/cleanup-target-edge-errors {:before prepared :action action :after corrupt})))
      (is (some #(= :CleanupTargets (:id %))
                (inv/edge-check {:before prepared :action action :after corrupt}))))
    (let [wrong (assoc-in pending [:env :cleanup-targets a [:custody-claim 0] :target-world] a)]
      (is (seq (inv/cleanup-target-errors wrong))))))

(deftest existing-nonempty-settlement-refuses-before-public-release
  (let [before (apply-actions (nested-worlds)
                              [{:t :t26 :k kc :op :unsupported-steps :kind :discard
                                :caller (m/execution-holder b sb)}
                               {:t :t27 :k kc :op :unsupported-steps :payload :nonempty
                                :bases {} :steps [{:id :adapter-step}]}])]
    (refuses before (request a) ::m/unsupported-world-release)
    (is (nil? (get-in before [:env :releases a])))
    (is (= :live (:status (m/wr before a))))))

(deftest queued-seal-keeps-its-committed-operation-when-self-holder-retires
  (let [holder [:holder 1]
        setup (apply-actions (m/init-state)
                             [{:t :t19 :w a :v b :k kb :scope [:root a] :systems #{}}
                              {:t :t04 :w b :e :holder :mode :deref}
                              {:t :t05 :w b :r holder :kind :await-once :debtor [:host :gate]}
                              {:t :t32 :k kb :successor moved-kb :op :move-to-run
                               :caller (m/execution-holder a [:root a])
                               :holder (m/execution-holder b holder) :acceptor (m/execution-holder b holder)}])
        seal {:t :t26 :w b :k moved-kb :kind :discard :op :queued-discard
              :caller (m/execution-holder b holder)}
        before (m/enqueue setup b {:action seal})
        action {:t :queued :w b}
        after (checked before action)
        [[claim-id debt]] (seq (get-in after [:env :cleanup-targets b]))
        edge {:before before :action action :after after}]
    ;; A restored queued action is an accepted core-model ingress even though
    ;; no native production producer currently emits this particular packet.
    (is (empty? (inv/check before)))
    (is (= :sealed (:disposition (m/cap after moved-kb))))
    (is (= :queued-discard (:op debt)))
    (is (= :queued-discard (get-in after [:custody :claims claim-id :settlement-op])))
    (is (= (:holder (m/cap after moved-kb)) [:cleanup claim-id]))
    (is (empty? (inv/cleanup-target-edge-errors edge)))
    (let [wrong (assoc-in after [:env :cleanup-targets b claim-id :op] :wrong-operation)]
      (is (seq (inv/cleanup-target-edge-errors (assoc edge :after wrong))))
      (is (some #(= :CleanupTargets (:id %)) (inv/edge-check (assoc edge :after wrong)))))))
