(ns org.replikativ.spindel.world.recovery-test
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.world.scope :as scope]
            [org.replikativ.spindel.yggdrasil :as ygg]))

(defn- await-cps [operation]
  (let [p (promise)]
    (operation #(deliver p [:ok %]) #(deliver p [:error %]))
    (let [[kind value] (deref p 10000 [:error (ex-info "recovery timed out" {})])]
      (if (= :ok kind) value (throw value)))))

(defn- fork! [s source grant]
  (:child-ctx (await-cps #(scope/fork! s source {:grant grant} %1 %2))))

(defn- ledger-authority [book grants returns]
  (reify scope/PResourceAuthority
    (grant! [_ source child amount]
      (when amount
        (swap! book (fn [b]
                      (when (< (get-in b [(:fork-id source) :balance] 0) amount)
                        (throw (ex-info "insufficient" {})))
                      (-> b (update-in [(:fork-id source) :balance] - amount)
                          (assoc (:fork-id child) {:balance amount :from (:fork-id source)}))))
        (grants child)))
    (return! [_ child]
      (returns child)
      (swap! book (fn [b]
                    (if-let [{:keys [balance from]} (get b (:fork-id child))]
                      (-> b (update-in [from :balance] + balance) (dissoc (:fork-id child)))
                      b)))
      nil)))

(deftest failed-copy-funding-keeps-live-children-and-preserves-source
  (let [root (context/create-execution-context)
        book (atom {(:fork-id root) {:balance 10}})
        armed? (atom false)
        granted (atom 0)
        returned (atom 0)
        auth (ledger-authority book
                               (fn [_]
                                 (when (and @armed? (= 2 (swap! granted inc)))
                                   (throw (ex-info "second grant acknowledgement lost" {}))))
                               (fn [_]
                                 (when (= 1 (swap! returned inc))
                                   (throw (ex-info "refund unavailable" {})))))
        s (scope/create {:authority auth :fork-opts {:systems :none}})
        lease (scope/begin-activity! s :test)
        other (scope/begin-activity! s :replacement)]
    (try
      (let [source (fork! s root 8)
            handle (first (scope/handles @s))]
        (reset! armed? true)
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"requires cleanup"
                              (await-cps #(scope/copy! s source 3 {:grants [2 2 2]} %1 %2))))
        (is (ygg/open-fork? handle))
        (is (= [handle] (scope/handles @s)))
        (is (= 2 (count (:recovery @s))) "the untouched third child was discarded without refund")
        (is (every? (comp ygg/open-fork? :handle val) (:recovery @s)))
        (is (zero? (:pending-forks @s)))
        (is (= 4 (get-in @book [(:fork-id source) :balance])))
        (is (thrown? clojure.lang.ExceptionInfo (fork! s source nil)))
        (is (thrown? clojure.lang.ExceptionInfo (await-cps (scope/release! s source))))
        (is (thrown? clojure.lang.ExceptionInfo (scope/begin-activity! s :new)))
        (is (false? (:admitted? (scope/exchange-activity! s other [{:kind :new}]))))
        (await-cps (scope/recover! s))
        (is (empty? (:recovery @s)))
        (is (zero? (:pending-forks @s)))
        (is (= 8 (get-in @book [(:fork-id source) :balance])))
        (is (ygg/open-fork? handle))
        (is (some? (fork! s source nil))))
      (finally
        (scope/end-activity! s other)
        (scope/end-activity! s lease)
        (await-cps (scope/discard! s))
        (is (= {(:fork-id root) {:balance 10}} @book))
        (context/stop-context! root)))))

(deftest failed-discard-does-not-repeat-a-successful-refund
  (let [root (context/create-execution-context)
        book (atom {(:fork-id root) {:balance 10}})
        returns (atom 0)
        discarded? (atom false)
        auth (ledger-authority book (fn [_] (throw (ex-info "grant acknowledgement lost" {})))
                               (fn [_] (swap! returns inc)))
        s (scope/create {:authority auth :fork-opts {:systems :none}})
        lease (scope/begin-activity! s :test)
        discard ygg/discard-fork!]
    (try
      (with-redefs [ygg/discard-fork! (fn [handle opts]
                                        (when (compare-and-set! discarded? false true)
                                          (throw (ex-info "discard unavailable" {})))
                                        (discard handle opts))]
        (is (thrown? clojure.lang.ExceptionInfo (fork! s root 2))))
      (is (= 1 @returns))
      (is (= 1 (count (:recovery @s))))
      (is (= 10 (get-in @book [(:fork-id root) :balance])))
      (await-cps (scope/recover! s))
      (is (= 1 @returns))
      (is (empty? (:recovery @s)))
      (finally
        (scope/end-activity! s lease)
        (await-cps (scope/discard! s))
        (context/stop-context! root)))))

(deftest partial-copy-construction-is-owned-and-never-refunded
  (let [root (context/create-execution-context)
        returns (atom 0)
        book (atom {(:fork-id root) {:balance 10}})
        auth (ledger-authority book (constantly nil) (fn [_] (swap! returns inc)))
        s (scope/create {:authority auth :fork-opts {:systems :none}})
        lease (scope/begin-activity! s :test)
        fork ygg/fork!]
    (try
      (let [source (fork! s root 8)
            calls (atom 0)
            raw (atom nil)]
        (with-redefs [ygg/fork! (fn [opts]
                                  (when (= 2 (swap! calls inc)) (throw (ex-info "construction failed" {})))
                                  (let [h (fork opts)] (reset! raw h) h))
                      ygg/discard-fork! (fn [_ _] (throw (ex-info "discard unavailable" {})))]
          (is (thrown? clojure.lang.ExceptionInfo
                       (await-cps #(scope/copy! s source 2 {:grants [2 2]} %1 %2)))))
        (is (zero? @returns))
        (is (= 1 (count (:recovery @s))))
        (is (ygg/open-fork? @raw))
        (await-cps (scope/recover! s))
        (is (zero? @returns))
        (is (not (ygg/open-fork? @raw)))
        (is (= 8 (get-in @book [(:fork-id source) :balance]))))
      (finally
        (scope/end-activity! s lease)
        (await-cps (scope/discard! s))
        (context/stop-context! root)))))

(deftest discard-atomically-rechecks-a-late-recovery-obligation
  (let [root (context/create-execution-context)
        book (atom {(:fork-id root) {:balance 10}})
        auth (ledger-authority book (constantly nil) (constantly nil))
        s (scope/create {:authority auth :fork-opts {:systems :none}})
        lease (scope/begin-activity! s :test)
        source (fork! s root 8)
        source-handle (first (scope/handles @s))
        raw (binding [ec/*execution-context* source]
              (ygg/fork! {:mode :frozen :systems :none :sync? true}))
        discard-owned (var-get #'scope/discard-owned!)]
    (try
      ;; Model construction that is still pending at the wrapper's snapshot.
      (swap! s update :pending-forks inc)
      (scope/end-activity! s lease)
      (with-redefs-fn {#'scope/discard-owned!
                       (fn [scope]
                        ;; It fails immediately before the authoritative CAS.
                         (swap! scope #(-> (#'scope/add-recovery % raw false)
                                           (update :pending-forks dec)))
                         (discard-owned scope))}
        #(is (thrown? clojure.lang.ExceptionInfo (await-cps (scope/discard! s)))))
      (is (ygg/open-fork? source-handle))
      (is (ygg/open-fork? raw))
      (is (= 8 (get-in @book [(:fork-id source) :balance])))
      (is (zero? (:pending-forks @s)))
      (await-cps (scope/recover! s))
      (finally
        (scope/end-activity! s lease)
        (await-cps (scope/recover! s))
        (when (ygg/open-fork? raw) (ygg/discard-fork! raw {}))
        (await-cps (scope/discard! s))
        (is (= {(:fork-id root) {:balance 10}} @book))
        (context/stop-context! root)))))
