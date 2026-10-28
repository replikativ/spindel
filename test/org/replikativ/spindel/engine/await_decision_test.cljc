(ns org.replikativ.spindel.engine.await-decision-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.core :as sc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :refer [async]]
            [is.simm.partial-cps.async :as pcps]))

;; Every callback runs synchronously in these tests. No blocking Spin derefs.
(deftest inline-production-keeps-its-supplied-result
  (async done
         (let [world (ctx/create-execution-context :executor (ex/synchronous-executor))]
           (binding [ec/*execution-context* world pcps/*in-trampoline* false]
             (let [child (spin :stored)
                   parent (spin nil)
                   sid (sc/spin-id parent)
                   result (sc/ok :produced)
                   cont {:id ::production :kind :await-reactive :body-slice? true
                         :event-key [:spin/complete (sc/spin-id child)]
                         :registration (random-uuid)}]
               (sync/spawn! child)
               (ec/continuation-add! sid cont)
          ;; A fresh inline production supplies its own certified wrapper;
          ;; cache delivery supplies nil instead. Forked code
          ;; can produce on this stack without updating this world's cache.
               (let [claimed (simple/claim-continuation-for-resume!
                              world sid (:id cont)
                              {:result result :registration (:registration cont) :inline? true})]
                 (is (some? claimed))
                 (is (identical? result ((:on-resume claimed) world)))))))
         (done)))

(deftest non-body-completions-use-the-supplied-result
  (async done
         (let [world (ctx/create-execution-context :executor (ex/synchronous-executor))]
           (binding [ec/*execution-context* world pcps/*in-trampoline* false]
             (let [parent (spin nil)
                   sid (sc/spin-id parent)
                   result (sc/ok :value)
                   cont {:id ::combinator :kind :await-reactive
                         :event-key [:spin/complete ::combinator-child]
                         :registration (random-uuid)}]
          ;; Combinators select their result themselves. They need no body
          ;; child node for the readiness check used by await slices.
               (ec/continuation-add! sid cont)
               (let [claimed (simple/claim-continuation-for-resume!
                              world sid (:id cont)
                              {:result result :registration (:registration cont) :inline? true})]
                 (is (some? claimed))
                 (is (identical? result ((:on-resume claimed) world)))))))
         (done)))

(deftest await-joins-a-local-execution-reservation
  (async done
         (let [world (ctx/create-execution-context :executor (ex/synchronous-executor))]
           (binding [ec/*execution-context* world pcps/*in-trampoline* false]
             (let [mailbox (sync/create-mailbox world)
                   runs (atom 0) values (atom [])
                   child (spin (swap! runs inc) (await mailbox))
                   observer (spin (await child))
                   claim! simple/try-claim-execution!]
               (with-redefs [simple/try-claim-execution!
                             (fn [rt sid]
                               (let [claimed? (claim! rt sid)]
                                 (when (and claimed? (= sid (sc/spin-id child)))
                                     ;; The event owns a start but has not entered
                                     ;; the body prologue yet. Its world is evidence
                                     ;; of a local completion route already.
                                   (sync/spawn! observer {:on-success #(swap! values conj %)}))
                                 claimed?))]
                 (simple/process-event! world {:type :spin-execution :id (sc/spin-id child)
                                               :spin child :resolve-fn identity :reject-fn identity}))
               (sync/post! mailbox :end)
               (is (= [:end] @values))
               (is (= 1 @runs)))))
         (done)))

(deftest invalidation-after-ready-decision
  (async done
         (let [world (ctx/create-execution-context :executor (ex/synchronous-executor))
               cb (atom nil) values (atom []) runs (atom 0)]
           (binding [ec/*execution-context* world pcps/*in-trampoline* false]
             (let [child (spin (if (= 1 (swap! runs inc))
                                 (await (fn [r _] (reset! cb r) sc/incomplete)) :new))
                   observer (spin (await child))
                   add! ec/continuation-add!
                   claim! simple/try-claim-execution!
                   resume! simple/claim-continuation-for-resume!
                   forced? (atom false)
                   dirty! (fn [rt]
                            (when (compare-and-set! forced? false true)
                              (simple/mark-dirty! rt (sc/spin-id child))))]
               (sync/spawn! child)
               (with-redefs [ec/continuation-add!
                             (fn [sid cont]
                               (when (= sid (sc/spin-id observer)) ((deref cb) :old))
                               (add! sid cont))
                               ;; Before the fix, dirty immediately after the failed
                               ;; execution claim. After it, dirty before the arbiter
                               ;; revalidates the ready decision. Both must refresh.
                             simple/try-claim-execution!
                             (fn hooked-claim
                               ([rt sid] (hooked-claim rt sid nil))
                               ([rt sid opts]
                                (let [claimed? (if opts (claim! rt sid opts) (claim! rt sid))]
                                  (when (and (= sid (sc/spin-id child)) (not claimed?)) (dirty! rt))
                                  claimed?)))
                             simple/claim-continuation-for-resume!
                             (fn hooked-resume
                               ([rt sid cid] (hooked-resume rt sid cid nil))
                               ([rt sid cid opts]
                                (when (= sid (sc/spin-id observer)) (dirty! rt))
                                (resume! rt sid cid opts)))]
                 (sync/spawn! observer {:on-success #(swap! values conj %)}))
               (is @forced?)
               (is (= [:new] @values))
               (is (= 2 @runs)))))
         (done)))

(deftest dirty-cancellation-during-registration-is-terminal
  (async done
         (let [world (ctx/create-execution-context :executor (ex/synchronous-executor))
               runs (atom 0) errors (atom [])]
           (binding [ec/*execution-context* world pcps/*in-trampoline* false]
             (let [child (spin (swap! runs inc) (await (fn [_ _] sc/incomplete)))
                   observer (spin (await child))
                   add! ec/continuation-add!]
               (sync/spawn! child {:on-error (fn [_])})
               (with-redefs [ec/continuation-add!
                             (fn [sid cont]
                               (when (= sid (sc/spin-id observer))
                                 (rtp/swap-state! world [:nodes (sc/spin-id child)] simple/invalidate-node)
                                 (sc/cancel-spin! child))
                               (add! sid cont))]
                 (sync/spawn! observer {:on-error #(swap! errors conj (:type (ex-data %)))}))
               (is (= [::sc/spin-cancelled] @errors))
               (is (= 1 @runs) "an invalidated cancellation must not restart"))))
         (done)))

(deftest ready-claim-selects-current-result
  (async done
         (let [world (ctx/create-execution-context :executor (ex/synchronous-executor))
               values (atom [])]
           (binding [ec/*execution-context* world pcps/*in-trampoline* false]
             (let [child (spin :old)
                   observer (spin (await child))
                   claim! simple/claim-continuation-for-resume!]
               (sync/spawn! child)
               (with-redefs [simple/claim-continuation-for-resume!
                             (fn hooked-claim
                               ([rt sid cid] (hooked-claim rt sid cid nil))
                               ([rt sid cid opts]
                                (when (= sid (sc/spin-id observer))
                                  (simple/cache-result! rt (sc/spin-id child) (sc/ok :new)))
                                (claim! rt sid cid opts)))]
                 (sync/spawn! observer {:on-success #(swap! values conj %)}))
               (is (= [:new] @values)))))
         (done)))

(deftest failed-execution-claims-do-not-copy-inherited-nodes
  (async done
         (let [parent (ctx/create-execution-context :executor (ex/synchronous-executor))]
           (binding [ec/*execution-context* parent pcps/*in-trampoline* false]
             (let [child (spin :old)]
               (sync/spawn! child)
               (let [fork (ctx/fork-context parent :mode :following)
                     sid (sc/spin-id child)]
                 (is (false? (simple/try-claim-execution! fork sid)))
                 (simple/cache-result! parent sid (sc/ok :new))
                 (is (= :new (:payload (rtp/current-result fork sid)))
                     "a non-start decision must leave the node following its parent")))))
         (done)))

(deftest fork-await-parent-run
  (async done
         (doseq [mode [:following :frozen]]
           (let [parent (ctx/create-execution-context :executor (ex/synchronous-executor))
                 callbacks (atom {})
                 vals (atom [])]
             (binding [ec/*execution-context* parent pcps/*in-trampoline* false]
               (let [child (spin (await (fn [r _] (swap! callbacks assoc (:fork-id (ec/current-execution-context)) r) sc/incomplete)))]
                 (sync/spawn! child)
                 (let [fork (ctx/fork-context parent :mode mode)]
                   (binding [ec/*execution-context* fork]
                     (sync/spawn! (spin (await child)) {:on-success #(swap! vals conj %) :on-error #(swap! vals conj [:error %])}))
                   (is (contains? @callbacks (:fork-id fork)) "foreign work must re-enter locally")
                   ((get @callbacks (:fork-id parent)) :parent-result)
                   (when-let [r (get @callbacks (:fork-id fork))]
                     (binding [ec/*execution-context* fork] (r :fork-result)))
                   (is (= [:fork-result] @vals) (str mode " observer must have a local delivery route")))))))
         (done)))

(deftest batch-join-does-not-deliver-old-cache
  (async done
         (let [world (ctx/create-execution-context :executor (ex/synchronous-executor))
               runs (atom 0) cb (atom nil) a (atom []) b (atom [])]
           (binding [ec/*execution-context* world pcps/*in-trampoline* false]
             (let [child (spin (if (= 1 (swap! runs inc)) :old
                                   (await (fn [r _] (reset! cb r) sc/incomplete))))]
               (sync/spawn! child)
               (ec/swap-state! [:engine/current-batch]
                               (constantly {:processed (atom #{}) :resumed-conts (atom #{}) :generation 100}))
               (sync/spawn! (spin (await child)) {:on-success #(swap! a conj %)})
               (sync/spawn! (spin (await child)) {:on-success #(swap! b conj %)})
               (is (empty? @a) "first await must wait for refreshed cache")
               (is (empty? @b) "second await must wait for refreshed cache")
               (ec/swap-state! [:engine/current-batch] (constantly nil))
               ((deref cb) :new)
               (is (= [:new] @a))
               (is (= [:new] @b))
               (is (= 2 @runs) "both parents share the refresh"))))
         (done)))

(deftest real-signal-batch-refresh
  (async done
         (let [world (ctx/create-execution-context :executor (ex/synchronous-executor))
               runs (atom 0) cb (atom nil) deliveries (atom [])]
           (binding [ec/*execution-context* world pcps/*in-trampoline* false]
             (let [source (sig/signal 0)
                   child (spin (if (= 1 (swap! runs inc)) :old
                                   (await (fn [r _] (reset! cb r) sc/incomplete))))
                   a (spin (track source) (let [v (await child)] (swap! deliveries conj [:a v]) v))
                   b (spin (track source) (let [v (await child)] (swap! deliveries conj [:b v]) v))]
               (sync/spawn! a)
               (sync/spawn! b)
               (reset! deliveries [])
               (reset! source 1)
               (is (empty? @deliveries) "both reactive siblings wait for refresh")
               ((deref cb) :new)
               (is (= #{[:a :new] [:b :new]} (set @deliveries)))
               (is (= 2 (count @deliveries)) "each suffix advances once")
               (is (= 2 @runs) "reactive siblings share the refresh"))))
         (done)))
