(ns org.replikativ.spindel.engine.native-legacy-boundary-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :refer [run-spin!]]))

(defn- refused-without-effects! [native legacy effects label operation]
  (testing (name label)
    (let [before (rtp/get-state legacy [])
          family (c/snapshot-family native)
          callbacks @effects
          error (try (operation) nil
                     (catch #?(:clj Throwable :cljs :default) error error))]
      (is (= {:error :unsupported-operation :operation :native-legacy-graph-entry}
             (select-keys (ex-data error) [:error :operation])))
      (is (= before (rtp/get-state legacy [])))
      (is (= family (c/snapshot-family native)))
      (is (= callbacks @effects)))))

(deftest native-frame-cannot-enter-a-selected-legacy-graph-or-producer
  (doseq [following? [false true]]
    (let [root (ctx/create-execution-context :engine :simple :executor (ex/synchronous-executor))
          legacy (if following? (ctx/fork-context root) root)
          native (c/runtime {:audit? true})
          effects (atom []) results (atom []) retained-cell (atom nil)
          gate (c/ticket :boundary)]
      (try
        (binding [ec/*execution-context* legacy]
          (let [target (spin (swap! effects conj :legacy-body) :legacy-result)
                id (spin-core/spin-id target) body (spin-core/spin-body target)
                signal (sig/signal 0)
                lazy-signal (sig/->SignalRef :uninitialized-boundary-signal 7)
                deferred (sync/deferred) mailbox (sync/mailbox)
                ok #(swap! effects conj [:ok %])
                fail #(swap! effects conj [:error %])
                _ (sync/post! mailbox :seed)
                _ (rtp/add-public-signal-watch! legacy signal :boundary
                                                (fn [& _] (swap! effects conj :watch)))
                ;; The native actor deliberately shares the real legacy Spin's
                ;; ID. Generic legacy cells must still belong to B Root,
                ;; rather than borrowing either world's apparent Run ID.
                actor (c/cspin native id
                               (let [owner (lifetime/current-scope (ec/current-execution-context))]
                                 (lifetime/with-owner owner
                                   (binding [ec/*execution-context* legacy]
                                     (is (ec/same-world? legacy (ec/current-execution-context)))
                                     (is (ec/same-world? native (rtp/context-scope-runner legacy)))
                                     (is (= (rtp/root-execution-owner legacy)
                                            (rtp/current-execution-owner legacy)))
                                     (let [cell (ratom/create-atom 10)
                                           cell-id (ratom/atom-id cell)]
                                       (reset! retained-cell cell)
                                       (is (= 11 (swap! cell inc)))
                                       (is (= 11 (rtp/runtime-cell-value legacy cell-id)))
                                       (is (= (rtp/root-execution-owner legacy)
                                              (rtp/get-state legacy [:atoms cell-id :lifetime/owner]))))
                                     (rtp/swap-state! legacy [:application :selected] (constantly :allowed))
                                     (is (= :allowed (rtp/get-state legacy [:application :selected])))
                                     ;; These are real typed callback entrypoints,
                                     ;; not hidden await/track calls inside fns.
                                     (doseq [[label operation]
                                             [[:construct #(spin (swap! effects conj :constructed-body) :new)]
                                              [:register #(rtp/register-computation! legacy target id body)]
                                              [:invoke #(rtp/invoke-computation! legacy target id body ok fail :callback)]
                                              [:await #(rtp/await-computation! legacy target id body id :boundary ok fail)]
                                              [:track #(rtp/track-public-signal! legacy signal id :boundary ok fail)]
                                              [:cancel #(rtp/cancel-computation! legacy target id body :forbidden)]
                                              [:graph-dependency #(rtp/track-spin-dep! legacy id :other)]
                                              [:enqueue #(rtp/enqueue! legacy {:type :signal-change :id (:id signal)})]
                                              [:deferred-factory #(sync/deferred)]
                                              [:deferred-claim #(deferred :forbidden)]
                                              [:deferred-deliver #(sync/deliver! deferred :forbidden)]
                                              [:deferred-invoke #(deferred ok fail)]
                                              [:mailbox-factory #(sync/mailbox)]
                                              [:mailbox-post #(sync/post! mailbox :forbidden)]
                                              [:mailbox-take #(sync/take-now! mailbox id)]
                                              [:mailbox-invoke #(mailbox ok fail)]
                                              [:mailbox-next #(rtp/invoke-public-mailbox-next! legacy mailbox ok fail)]
                                              [:signal-factory #(sig/signal (do (swap! effects conj :signal-init) 1))]
                                              [:signal-lazy-value #(rtp/public-signal-value legacy lazy-signal)]
                                              [:signal-lazy-state #(rtp/public-signal-state legacy lazy-signal)]
                                              [:signal-swap #(rtp/swap-public-signal!
                                                              legacy signal
                                                              (fn [v] (swap! effects conj :mutation) (inc v))
                                                              [] true (fn [] (swap! effects conj :committed)) true)]
                                              [:signal-cas #(rtp/cas-public-signal! legacy signal 0 1 true)]]]
                                       (refused-without-effects! native legacy effects label operation)))))
                               (is (ec/same-world? native (ec/current-execution-context)))
                               (c/park gate))]
            (c/observe! native actor #(swap! results conj [:ok %]) #(swap! results conj [:error %]))
            (is (empty? @results))
            (is (empty? @effects))
            (is (= :parked (get-in (c/snapshot native) [:runs [id 1] :status])))
            ;; Retiring the actual A Run must not revoke or re-own app data
            ;; deliberately allocated in the selected legacy B world.
            (let [before (rtp/get-state legacy [])]
              (c/cancel-spin! native actor)
              (is (= [:error] (mapv first @results)))
              (is (= before (rtp/get-state legacy []))))
            (is (= 11 (rtp/runtime-cell-value legacy (ratom/atom-id @retained-cell))))
            (is (= (rtp/root-execution-owner legacy)
                   (rtp/get-state legacy [:atoms (ratom/atom-id @retained-cell) :lifetime/owner])))
            (is (nil? (rtp/get-state legacy [:nodes (:id lazy-signal)])))
            ;; Once the physical native frame has returned, these same legacy
            ;; handles retain their ordinary public behavior.
            (run-spin! target #(swap! effects conj [:result %]) fail)
            (is (= [:legacy-body [:result :legacy-result]] @effects))
            (deferred ok fail)
            (sync/deliver! deferred 42)
            (is (= {:assigned? true :value 42} (rtp/read-public-deferred legacy deferred)))
            (is (= [:ok 42] (last @effects)))
            (is (= :seed (sync/take-now! mailbox :outside-native)))
            (is (= 7 (rtp/public-signal-value legacy lazy-signal)))
            (is (some? (rtp/get-state legacy [:nodes (:id lazy-signal)])))
            (is (= 1 (:value (rtp/swap-public-signal! legacy signal inc [] true nil false))))
            (is (= :watch (last @effects)))
            (let [reader (spin (+ (await deferred) (iv/get-new (track signal))))]
              (run-spin! reader #(swap! effects conj [:legacy-await-track %]) fail)
              (is (= [:legacy-await-track 43] (last @effects))))
            (verify-boundaries! native)))
        (finally
          ;; Hold cell/handles through state checks; all dispatch is synchronous.
          (when following? (ctx/stop-context! legacy))
          (ctx/stop-context! root))))))
