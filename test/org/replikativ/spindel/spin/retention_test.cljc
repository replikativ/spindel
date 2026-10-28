(ns org.replikativ.spindel.spin.retention-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.core :as sc]
            [org.replikativ.spindel.spin.keyed :as keyed]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

(defn- keep-reachable! [& xs]
  #?(:clj (doseq [x xs] (java.lang.ref.Reference/reachabilityFence x))
     :cljs nil))

(defn- complete! [s]
  ;; These tests use a synchronous executor, including event dispatch. Check
  ;; cleanup after invocation returns, outside the completion callback/drain.
  (run-spin! s (fn [_]) (fn [e] (is false (str e)))))

(defn- assert-absent! [world sid]
  (doseq [path [[:nodes] [:spins-meta] [:track-subscriptions] [:await-conts]
                [:pending-callbacks] [:run-callbacks] [:spin-tracking]
                [:addressing :chain-heads] [:addressing :occurrences]
                [:keyed] [:keyed/spins] [:engine/spawned]]]
    ;; A nil occurrence row (e.g. after fork-local seeding) must go too.
    (is (not (contains? (rtp/get-state world path) sid)) (str path)))
  (is (not (contains? (rtp/get-state world [:engine/reuse-barriers]) sid))))

(deftest completed-spin-releases-addressing-rows
  (async done
         (with-ctx [world]
           (let [world (assoc world :executor (ex/synchronous-executor))]
             (binding [ec/*execution-context* world]
               (let [s (spin (addressing/site-address! (ec/current-execution-context) "effect" :savepoint :site))
                     sid (sc/spin-id s)]
                 (complete! s)
                 (doseq [table [:chain-heads :occurrences]]
                   (is (contains? (rtp/get-state world [:addressing table]) sid)))
                 (rtp/enqueue! world {:type :gc-cleanup :id sid})
                 (assert-absent! world sid)
                 (keep-reachable! s)
                 (done)))))))

(deftest full-cleanup-releases-keyed-registries-and-reuse-barriers
  (async done
         (with-ctx [world]
           (let [world (assoc world :executor (ex/synchronous-executor))]
             (binding [ec/*execution-context* world]
               (let [s (keyed/keyed :items [1 2] (fn [k] (spin k)))
                     sid (sc/spin-id s)]
                 (complete! s)
                 (let [children (vals (keyed/children sid))]
                   (is (= 2 (count children)))
                   (simple/mark-reuse-barrier! world sid)
                   (is (contains? (rtp/get-state world [:engine/reuse-barriers]) sid))
                   (rtp/swap-state! world [:engine/spawned] #(assoc % sid s))
                   (simple/full-cleanup-spin! world sid)
                   (assert-absent! world sid)
                   (doseq [child children]
                     (is (nil? (keyed/spin-of world (sc/spin-id child))))))
                 (keep-reachable! s)
                 (done)))))))

(deftest cleanup-is-local-to-fork-and-preserves-live-addressing
  (async done
         (with-ctx [parent]
           (let [parent (assoc parent :executor (ex/synchronous-executor))]
             (binding [ec/*execution-context* parent]
               (let [s (spin (addressing/site-address! (ec/current-execution-context) "effect" :savepoint :site))
                     sid (sc/spin-id s)]
                 (complete! s)
                 (doseq [mode [:following :frozen]]
                   (let [fork (ctx/fork-context parent :mode mode :executor (ex/synchronous-executor))]
                     (try
                  ;; Read-through nodes are not the fork's to reclaim.
                       (rtp/enqueue! fork {:type :gc-cleanup :id sid})
                       (is (some? (rtp/get-state fork [:nodes sid])))
                  ;; Own the node, as a fork body re-entry does, then reap it.
                       (rtp/swap-state! fork [:nodes sid] #(assoc % :orphaned? true))
                       (addressing/seed-body-chain-head! fork sid)
                       (rtp/enqueue! fork {:type :gc-cleanup :id sid})
                       (assert-absent! fork sid)
                       (is (some? (rtp/get-state parent [:nodes sid])))
                       (is (contains? (rtp/get-state parent [:addressing :chain-heads]) sid))
                       (is (contains? (rtp/get-state parent [:addressing :occurrences]) sid))
                       (finally (ctx/close-context! fork)))))
            ;; Clearing dependencies is not reclamation: preserve the cursor
            ;; and counters so a suspended/re-running body keeps its identity.
                 (binding [ec/*spin-id* sid]
                   (addressing/next-address! parent "child" :site)
                   (addressing/site-address! parent "effect" :savepoint :site))
                 (let [before (rtp/get-state parent [:addressing])]
                   (simple/clear-deps! parent sid)
                   (is (= before (rtp/get-state parent [:addressing]))))
                 (keep-reachable! s)
                 (done)))))))

(deftest superseded-orphan-releases-addressing-rows
  (async done
         (with-ctx [world]
           (let [world (assoc world :executor (ex/synchronous-executor))]
             (binding [ec/*execution-context* world]
               (let [parent (spin :parent)
                     child (spin :child)
                     pid (sc/spin-id parent)
                     cid (sc/spin-id child)]
                 (complete! parent)
                 (complete! child)
            ;; A completed creator dropped its now-orphaned child. The
            ;; supersession path reaps it in the same transaction.
                 (rtp/swap-state! world [:nodes cid] #(assoc % :created-by pid :orphaned? true))
                 (rtp/swap-state! world [:nodes pid] #(assoc % :dropped-children #{cid}))
                 (simple/mark-reuse-barrier! world cid)
                 (simple/release-superseded-children! world pid)
                 (assert-absent! world cid)
                 (is (contains? (rtp/get-state world [:addressing :chain-heads]) pid))
                 (keep-reachable! parent child)
                 (done)))))))

(deftest body-rerun-keeps-deterministic-addresses-until-reclamation
  (async done
         (with-ctx [world]
           (let [world (assoc world :executor (ex/synchronous-executor))]
             (binding [ec/*execution-context* world]
               (let [s (spin [(addressing/next-address! (ec/current-execution-context) "child" :site)
                              (addressing/site-address! (ec/current-execution-context) "effect" :savepoint :site)])
                     sid (sc/spin-id s)
                     results (atom [])]
                 (run-spin! s #(swap! results conj %) #(is false (str %)))
                 (is (seq (addressing/get-occurrences world sid)))
                 (rtp/mark-dirty! world sid)
                 (run-spin! s #(swap! results conj %) #(is false (str %)))
                 (is (= 2 (count @results)))
                 (is (apply = @results))
            ;; Another live spin and the global cursor must survive this reap.
                 (let [other (spin (addressing/site-address! (ec/current-execution-context) "effect" :savepoint :other))
                       oid (sc/spin-id other)]
                   (complete! other)
                   (let [head (rtp/get-state world [:addressing :chain-head])]
                     (rtp/enqueue! world {:type :gc-cleanup :id sid})
                     (is (= head (rtp/get-state world [:addressing :chain-head]))))
                   (assert-absent! world sid)
                   (is (contains? (rtp/get-state world [:addressing :chain-heads]) oid))
                   (is (contains? (rtp/get-state world [:addressing :occurrences]) oid))
                   (keep-reachable! other))
                 (keep-reachable! s)
                 (done)))))))

(deftest keyed-cleanup-preserves-children-held-by-another-container
  (async done
         (with-ctx [world]
           (let [world (assoc world :executor (ex/synchronous-executor))]
             (binding [ec/*execution-context* world]
               (let [shared (spin :shared)
                     sid (sc/spin-id shared)
                     alias (sc/->Spin sid (sc/spin-body shared))
                     a (keyed/keyed :a [1] (fn [_] shared))
                     b (keyed/keyed :b [1] (fn [_] alias))]
                 (complete! a)
                 (complete! b)
            ;; Distinct handles may name the same structural spin. Release
            ;; registrations by ID, and only after the last container goes.
                 (simple/full-cleanup-spin! world (sc/spin-id b))
                 (is (some? (keyed/spin-of world sid)))
                 (simple/full-cleanup-spin! world (sc/spin-id a))
                 (is (nil? (keyed/spin-of world sid)))
                 (keep-reachable! shared alias a b)
                 (done)))))))

(deftest cleanup-shares-untouched-subscriptions-and-skips-absent-tables
  (async done
         (with-ctx [world]
           (let [unrelated {[:signal :live] {:other #{:live-cont}}}
                 absent [:pending-callbacks :run-callbacks :spin-tracking]]
             (rtp/swap-state! world []
                              #(assoc (apply dissoc % absent) :subscriptions unrelated))
             (simple/full-cleanup-spin! world :reclaimed)
             (is (identical? unrelated (rtp/get-state world [:subscriptions])))
             (doseq [table absent]
               (is (not (contains? (rtp/get-state world []) table))))
        ;; A reverse edge can remain after its continuation is gone. Reclaim
        ;; it too, keep other subscribers, and prune empty event buckets.
             (rtp/swap-state! world [:subscriptions]
                              #(assoc % [:spin/complete :child] {:reclaimed #{:old} :other #{:live}}
                                      [:external-await :old] {:reclaimed #{:retired}}
                                      [:external-await :empty] {}))
             (simple/full-cleanup-spin! world :reclaimed)
             (let [subs (rtp/get-state world [:subscriptions])]
               (is (= {[:signal :live] {:other #{:live-cont}}
                       [:spin/complete :child] {:other #{:live}}} subs))
               (is (identical? (get unrelated [:signal :live])
                               (get subs [:signal :live]))))
             (done)))))
