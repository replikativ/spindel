(ns org.replikativ.spindel.savepoint.portable-test
  "Law 5: hydrating a persisted savepoint is resuming a fork of it."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.edn :as edn]
            [org.replikativ.spindel.effects.savepoint :as sp :refer [savepoint]]
            [org.replikativ.spindel.effects.await :as aw]
            [org.replikativ.spindel.savepoint.portable :as portable]
            [org.replikativ.spindel.engine.component :as component]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.world.scope :as world-scope]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [outcome (deref result 5000 ::timeout)]
      (when (= ::timeout outcome) (throw (ex-info "CPS operation timed out" {})))
      (if (= :ok (first outcome)) (second outcome) (throw (second outcome))))))

(defn- take! [queue]
  (or (.poll ^java.util.concurrent.LinkedBlockingQueue queue 5 java.util.concurrent.TimeUnit/SECONDS)
      (throw (ex-info "No savepoint event arrived" {}))))

(defn- log! [k answer]
  (rtp/swap-state! ec/*execution-context* [:conversation :log]
                   (fn [log] (conj (or log []) [k answer]))))

(declare after-turn)

(defn conversation
  "Three turns; every turn is a portable savepoint. Returns the log."
  [from]
  (spin
   (loop [k from]
     (if (< k 3)
       (let [answer (savepoint :conversation/turn {:turn k}
                               {:resume `after-turn :args [k] :state [[:conversation]]})]
         (log! k answer)
         (recur (inc k)))
       (rtp/get-state ec/*execution-context* [:conversation :log])))))

(defn after-turn
  "What the continuation of turn `k` does, as a function of the answer."
  [k answer]
  (spin
   (log! k answer)
   (aw/await (conversation (inc k)))))

(defn- drive!
  "Answer every turn of whatever reports to `events` with `(answer k)` until a
  terminal event; returns its payload."
  [events answer]
  (loop []
    (let [event (take! events)]
      (if (:savepoint/terminal? event)
        (:savepoint/payload event)
        (do (sp/resume event (answer (:turn (:savepoint/payload event))))
            (recur))))))

(deftest hydrating-a-persisted-savepoint-is-resuming-a-fork-of-it
  (let [root (context/create-execution-context)
        events (java.util.concurrent.LinkedBlockingQueue.)
        session (sp/open! root {:seed 7 :fork-opts {:systems :none}
                                :handlers {sp/any-site #(.put events %)}})]
    (try
      (sp/start! session (binding [ec/*execution-context* root] (conversation 0)))
      (sp/resume (take! events) :a0)
      (let [turn-1 (take! events)
            data (await-cps (portable/persist turn-1))
            wire (edn/read-string (pr-str data))]
        (testing "the portable form is plain data with a content id"
          (is (= data wire))
          (is (= {:fn `after-turn :args [1]} (:savepoint/resume data)))
          (is (= {[:conversation] {:log [[0 :a0]]}} (:world/state data)))
          (is (some? (:savepoint/id data))))
        (testing "persisting does not consume the savepoint"
          (is (sp/pending? turn-1)))
        (let [forked (await-cps (sp/fork turn-1))
              _ (sp/resume forked :b1)
              in-process (drive! events (fn [k] (keyword (str "b" k))))
              _ (await-cps (portable/hydrate! session wire :b1))
              hydrated (drive! events (fn [k] (keyword (str "b" k))))]
          (is (= [[0 :a0] [1 :b1] [2 :b2]] in-process))
          (is (= in-process hydrated)))
        (testing "and the original still goes its own way"
          (sp/resume turn-1 :a1)
          (is (= [[0 :a0] [1 :a1] [2 :a2]] (drive! events (fn [k] (keyword (str "a" k))))))))
      (finally
        (await-cps (sp/close! session))
        (context/stop-context! root)))))

(deftest a-savepoint-without-a-resume-function-is-not-portable
  (let [root (context/create-execution-context)
        events (java.util.concurrent.LinkedBlockingQueue.)
        session (sp/open! root {:fork-opts {:systems :none}
                                :handlers {sp/any-site #(.put events %)}})]
    (try
      (sp/start! session (binding [ec/*execution-context* root]
                           (spin (savepoint :plain 1))))
      (is (= ::portable/not-portable
             (:type (ex-data (try (await-cps (portable/persist (take! events)))
                                  (catch Throwable error error))))))
      (finally
        (await-cps (sp/close! session))
        (context/stop-context! root)))))

(deftest a-hydrated-world-reads-the-parameters-it-was-persisted-under
  (let [root (context/create-execution-context)
        store (atom {0 {:w 1.0} 1 {:w 2.0}})
        events (java.util.concurrent.LinkedBlockingQueue.)
        params (binding [ec/*execution-context* root]
                 (component/register! :policy/params
                                      (component/pinned store 0 (fn [s v] (get @s v)))))
        session (sp/open! root {:fork-opts {:systems :none}
                                :handlers {sp/any-site #(.put events %)}})]
    (try
      (sp/start! session (binding [ec/*execution-context* root] (conversation 0)))
      (let [data (await-cps (portable/persist (take! events)))]
        (is (= {:policy/params 0} (:world/pinned data)))
        ;; the trainer moves on; the host world now reads version 1
        (binding [ec/*execution-context* root] (component/repin! params 1))
        (let [world (await-cps (portable/hydrate! session data :x))]
          (is (= 0 (component/pinned-version world params)))
          (is (= {:w 1.0} (component/resolve-in world params)))))
      (finally
        (await-cps (sp/close! session))
        (context/stop-context! root)))))

(defn- escrow-authority [ledger]
  (reify world-scope/PResourceAuthority
    (grant! [_ source child amount]
      (swap! ledger #(-> % (update-in [:wallets (:fork-id source)] - amount)
                         (assoc-in [:wallets (:fork-id child)] amount)))
      nil)
    (return! [_ _context] nil)
    (escrow! [_ context key]
      (swap! ledger (fn [book]
                      (let [left (get-in book [:wallets (:fork-id context)] 0)]
                        (-> book
                            (assoc-in [:wallets (:fork-id context)] 0)
                            (assoc-in [:escrow key] left)))))
      nil)
    (claim! [_ key context]
      (let [[before _] (swap-vals! ledger
                                   (fn [book]
                                     (if-let [amount (get-in book [:escrow key])]
                                       (-> book
                                           (update :escrow dissoc key)
                                           (assoc-in [:wallets (:fork-id context)] amount))
                                       book)))]
        (when-not (contains? (:escrow before) key)
          (throw (ex-info "Escrow already claimed" {:type ::claimed})))
        nil))))

(deftest authority-leaves-with-the-savepoint-and-arrives-once
  (let [root (context/create-execution-context)
        ledger (atom {:wallets {(:fork-id root) 10} :escrow {}})
        events (java.util.concurrent.LinkedBlockingQueue.)
        session (sp/open! root {:fork-opts {:systems :none}
                                :authority (escrow-authority ledger)
                                :handlers {sp/any-site #(.put events %)}})]
    (try
      (sp/start! session (binding [ec/*execution-context* root] (conversation 0)))
      (let [data (await-cps (portable/persist (take! events)))
            total #(+ (reduce + (vals (:wallets @ledger))) (reduce + (vals (:escrow @ledger))))]
        (is (= 10 (get-in @ledger [:escrow (:savepoint/id data)])))
        (is (zero? (get-in @ledger [:wallets (:fork-id root)])) "the world kept nothing")
        (let [world (await-cps (portable/hydrate! session data :x))]
          (is (= 10 (get-in @ledger [:wallets (:fork-id world)])))
          (is (= 10 (total))))
        (testing "the same data cannot bring the authority a second time"
          (let [outcome (try (await-cps (portable/hydrate! session data :x))
                             (catch Throwable error error))]
            (is (instance? Throwable outcome) (str "second hydration: " (pr-str outcome)))
            (is (= ::claimed (:type (ex-data outcome))) (str (when (instance? Throwable outcome) (ex-message outcome)))))
          (is (= 10 (total)))))
      (finally
        (await-cps (sp/close! session))
        (context/stop-context! root)))))
